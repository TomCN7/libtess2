/*
** SGI FREE SOFTWARE LICENSE B (Version 2.0, Sept. 18, 2008) 
** Copyright (C) [dates of first publication] Silicon Graphics, Inc.
** All Rights Reserved.
**
** Permission is hereby granted, free of charge, to any person obtaining a copy
** of this software and associated documentation files (the "Software"), to deal
** in the Software without restriction, including without limitation the rights
** to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
** of the Software, and to permit persons to whom the Software is furnished to do so,
** subject to the following conditions:
** 
** The above copyright notice including the dates of first publication and either this
** permission notice or a reference to http://oss.sgi.com/projects/FreeB/ shall be
** included in all copies or substantial portions of the Software. 
**
** THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
** INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
** PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL SILICON GRAPHICS, INC.
** BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
** TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE
** OR OTHER DEALINGS IN THE SOFTWARE.
** 
** Except as contained in this notice, the name of Silicon Graphics, Inc. shall not
** be used in advertising or otherwise to promote the sale, use or other dealings in
** this Software without prior written authorization from Silicon Graphics, Inc.
*/
/*
** Author: Eric Veach, July 1994.
*/

#include <stddef.h>
#include <assert.h>
#include <setjmp.h>
#include "bucketalloc.h"
#include "tess.h"
#include "mesh.h"
#include "sweep.h"
#include "geom.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define TRUE 1
#define FALSE 0

#define Dot(u,v)	(u[0]*v[0] + u[1]*v[1] + u[2]*v[2])

static void Normalize(float v[3])
{
	float len = v[0]*v[0] + v[1]*v[1] + v[2]*v[2];

	assert (len > 0) ;
	len = sqrtf (len) ;
	v[0] /= len;
	v[1] /= len;
	v[2] /= len;
}

#define ABS(x)	((x) < 0 ? -(x) : (x))

static int LongAxis(float v[3])
{
	int i = 0;

	if (ABS(v[1]) > ABS(v[0]))  { i = 1; }
	if (ABS(v[2]) > ABS(v[i]))  { i = 2; }
	return i;
}

static void ComputeNormal(TTesselator *pTess, float fNorm[3])
{
	TVertex *v, *v1, *v2;
	float c, tLen2, maxLen2;
	float maxVal[3], minVal[3], d1[3], d2[3], tNorm[3];
	TVertex *maxVert[3], *minVert[3];
	TVertex *vHead = &pTess->pMesh->vHead;
	int i;

	v = vHead->pNext;
	for (i = 0; i < 3; ++i) 
    {
		c = v->fCoords[i];
		minVal[i] = c;
		minVert[i] = v;
		maxVal[i] = c;
		maxVert[i] = v;
	}

	for (v = vHead->pNext; v != vHead; v = v->pNext) 
    {
		for (i = 0; i < 3; ++i) 
        {
			c = v->fCoords[i];
			if (c < minVal[i]) { minVal[i] = c; minVert[i] = v; }
			if (c > maxVal[i]) { maxVal[i] = c; maxVert[i] = v; }
		}
	}

	/* Find two vertices separated by at least 1/sqrt(3) of the maximum
	* distance between any two vertices
	*/
	i = 0;
	if (maxVal[1] - minVal[1] > maxVal[0] - minVal[0]) { i = 1; }
	if (maxVal[2] - minVal[2] > maxVal[i] - minVal[i]) { i = 2; }
	if (minVal[i] >= maxVal[i]) 
    {
		/* All vertices are the same -- normal doesn't matter */
		fNorm[0] = 0; fNorm[1] = 0; fNorm[2] = 1;
		return;
	}

	/* Look for a third vertex which forms the triangle with maximum area
	* (Length of normal == twice the triangle area)
	*/
	maxLen2 = 0;
	v1 = minVert[i];
	v2 = maxVert[i];
	d1[0] = v1->fCoords[0] - v2->fCoords[0];
	d1[1] = v1->fCoords[1] - v2->fCoords[1];
	d1[2] = v1->fCoords[2] - v2->fCoords[2];
	for (v = vHead->pNext; v != vHead; v = v->pNext) 
    {
		d2[0] = v->fCoords[0] - v2->fCoords[0];
		d2[1] = v->fCoords[1] - v2->fCoords[1];
		d2[2] = v->fCoords[2] - v2->fCoords[2];
		tNorm[0] = d1[1]*d2[2] - d1[2]*d2[1];
		tNorm[1] = d1[2]*d2[0] - d1[0]*d2[2];
		tNorm[2] = d1[0]*d2[1] - d1[1]*d2[0];
		tLen2 = tNorm[0]*tNorm[0] + tNorm[1]*tNorm[1] + tNorm[2]*tNorm[2];
		if (tLen2 > maxLen2) 
        {
			maxLen2 = tLen2;
			fNorm[0] = tNorm[0];
			fNorm[1] = tNorm[1];
			fNorm[2] = tNorm[2];
		}
	}

	if (maxLen2 <= 0) 
    {
		/* All points lie on a single line -- any decent normal will do */
		fNorm[0] = fNorm[1] = fNorm[2] = 0;
		fNorm[LongAxis(d1)] = 1;
	}
}


static void CheckOrientation(TTesselator *pTess)
{
	float fArea;
	TFace *pFace, *pfHead = &pTess->pMesh->fHead;
	TVertex *pVertex, *pvHead = &pTess->pMesh->vHead;
	THalfEdge *pEdge;

	/* When we compute the normal automatically, we choose the orientation
	* so that the the sum of the signed areas of all contours is non-negative.
	*/
	fArea = 0;
	for (pFace = pfHead->pNext; pFace != pfHead; pFace = pFace->pNext) 
    {
		pEdge = pFace->pHalfEdge;
		if (pEdge->nWinding <= 0) continue;
		do 
        {
			fArea += (pEdge->pOrigin->s - pEdge->Dst->s) * (pEdge->pOrigin->t + pEdge->Dst->t);
			pEdge = pEdge->Lnext;
		} while (pEdge != pFace->pHalfEdge);
	}
	if (fArea < 0) 
    {
		/* Reverse the orientation by flipping all the t-coordinates */
		for (pVertex = pvHead->pNext; pVertex != pvHead; pVertex = pVertex->pNext) 
        {
			pVertex->t = - pVertex->t;
		}
		pTess->ftUnit[0] = - pTess->ftUnit[0];
		pTess->ftUnit[1] = - pTess->ftUnit[1];
		pTess->ftUnit[2] = - pTess->ftUnit[2];
	}
}

#ifdef FOR_TRITE_TEST_PROGRAM
#include <stdlib.h>
extern int RandomSweep;
#define S_UNIT_X	(RandomSweep ? (2*drand48()-1) : 1.0)
#define S_UNIT_Y	(RandomSweep ? (2*drand48()-1) : 0.0)
#else
#if defined(SLANTED_SWEEP) 
/* The "feature merging" is not intended to be complete.  There are
* special cases where edges are nearly parallel to the sweep line
* which are not implemented.  The algorithm should still behave
* robustly (ie. produce a reasonable tesselation) in the presence
* of such edges, however it may miss features which could have been
* merged.  We could minimize this effect by choosing the sweep line
* direction to be something unusual (ie. not parallel to one of the
* coordinate axes).
*/
#define S_UNIT_X	(float)0.50941539564955385	/* Pre-normalized */
#define S_UNIT_Y	(float)0.86052074622010633
#else
#define S_UNIT_X	(float)1.0
#define S_UNIT_Y	(float)0.0
#endif
#endif

/* Determine the polygon normal and project vertices onto the plane
* of the polygon.
*/
void tessProjectPolygon(TTesselator *pTess)
{
	TVertex *v, *vHead = &pTess->pMesh->vHead;
	float fNorm[3];
	float *sUnit, *tUnit;
	int i, first, computedNormal = FALSE;

	fNorm[0] = pTess->fNormal[0];
	fNorm[1] = pTess->fNormal[1];
	fNorm[2] = pTess->fNormal[2];
	if (fNorm[0] == 0 && fNorm[1] == 0 && fNorm[2] == 0) 
    {
		ComputeNormal(pTess, fNorm);
		computedNormal = TRUE;
	}
	sUnit = pTess->fsUnit;
	tUnit = pTess->ftUnit;
	i = LongAxis(fNorm);

#if defined(FOR_TRITE_TEST_PROGRAM) || defined(TRUE_PROJECT)
	/* Choose the initial sUnit vector to be approximately perpendicular
	* to the normal.
	*/
	Normalize(fNorm);

	sUnit[i] = 0;
	sUnit[(i+1)%3] = S_UNIT_X;
	sUnit[(i+2)%3] = S_UNIT_Y;

	/* Now make it exactly perpendicular */
	w = Dot (sUnit, fNorm) ;
	sUnit[0] -= w * fNorm[0];
	sUnit[1] -= w * fNorm[1];
	sUnit[2] -= w * fNorm[2];
	Normalize (sUnit) ;

	/* Choose tUnit so that (sUnit,tUnit,norm) form a right-handed frame */
	tUnit[0] = fNorm[1]*sUnit[2] - fNorm[2]*sUnit[1];
	tUnit[1] = fNorm[2]*sUnit[0] - fNorm[0]*sUnit[2];
	tUnit[2] = fNorm[0]*sUnit[1] - fNorm[1]*sUnit[0];
	Normalize (tUnit) ;
#else
	/* Project perpendicular to a coordinate axis -- better numerically */
	sUnit[i] = 0;
	sUnit[(i+1)%3] = S_UNIT_X;
	sUnit[(i+2)%3] = S_UNIT_Y;

	tUnit[i] = 0;
	tUnit[(i+1)%3] = (fNorm[i] > 0) ? -S_UNIT_Y : S_UNIT_Y;
	tUnit[(i+2)%3] = (fNorm[i] > 0) ? S_UNIT_X : -S_UNIT_X;
#endif

	/* Project the vertices onto the sweep plane */
	for (v = vHead->pNext; v != vHead; v = v->pNext)
	{
		v->s = Dot(v->fCoords, sUnit);
		v->t = Dot(v->fCoords, tUnit);
	}
	if (computedNormal) 
    {
		CheckOrientation(pTess);
	}

	/* Compute ST bounds. */
	first = 1;
	for (v = vHead->pNext; v != vHead; v = v->pNext)
	{
		if (first)
		{
			pTess->fBMin[0] = pTess->fBMax[0] = v->s;
			pTess->fBMin[1] = pTess->fBMax[1] = v->t;
			first = 0;
		}
		else
		{
			if (v->s < pTess->fBMin[0]) pTess->fBMin[0] = v->s;
			if (v->s > pTess->fBMax[0]) pTess->fBMax[0] = v->s;
			if (v->t < pTess->fBMin[1]) pTess->fBMin[1] = v->t;
			if (v->t > pTess->fBMax[1]) pTess->fBMax[1] = v->t;
		}
	}
}

#define AddWinding(eDst,eSrc)	(eDst->winding += eSrc->winding, \
	eDst->Sym->winding += eSrc->Sym->winding)

/* tessMeshTessellateMonoRegion (face)  tessellates a monotone region
* (what else would it do??)  The region must consist of a single
* loop of half-edges (see mesh.h) oriented CCW.  "Monotone" in this
* case means that any vertical line intersects the interior of the
* region in a single interval.  
*
* Tessellation consists of adding interior edges (actually pairs of
* half-edges), to split the region into non-overlapping triangles.
*
* The basic idea is explained in Preparata and Shamos (which I don''t
* have handy right now), although their implementation is more
* complicated than this one.  The are two edge chains, an upper chain
* and a lower chain.  We process all vertices from both chains in order,
* from right to left.
*
* The algorithm ensures that the following invariant holds after each
* vertex is processed: the untessellated region consists of two
* chains, where one chain (say the upper) is a single edge, and
* the other chain is concave.  The left vertex of the single edge
* is always to the left of all vertices in the concave chain.
*
* Each step consists of adding the rightmost unprocessed vertex to one
* of the two chains, and forming a fan of triangles from the rightmost
* of two chain endpoints.  Determining whether we can add each triangle
* to the fan is a simple orientation test.  By making the fan as large
* as possible, we restore the invariant (check it yourself).
*/
int tessMeshTessellateMonoRegion(TMesh *pMesh, TFace *pFace)
{
	THalfEdge *up, *lo;

	/* All edges are oriented CCW around the boundary of the region.
	* First, find the half-edge whose origin vertex is rightmost.
	* Since the sweep goes from left to right, face->anEdge should
	* be close to the edge we want.
	*/
	up = pFace->pHalfEdge;
	assert(up->Lnext != up && up->Lnext->Lnext != up);

	for(; VertLeq(up->Dst, up->pOrigin); up = up->Lprev);
	for(; VertLeq(up->pOrigin, up->Dst); up = up->Lnext);
	lo = up->Lprev;

	while (up->Lnext != lo) 
    {
		if (VertLeq(up->Dst, lo->pOrigin)) 
        {
			/* up->Dst is on the left.  It is safe to form triangles from lo->Org.
			* The EdgeGoesLeft test guarantees progress even when some triangles
			* are CW, given that the upper and lower chains are truly monotone.
			*/
			while (lo->Lnext != up && (EdgeGoesLeft(lo->Lnext)
				|| EdgeSign(lo->pOrigin, lo->Dst, lo->Lnext->Dst) <= 0)) 
            {
					THalfEdge *tempHalfEdge= tessMeshConnect(pMesh, lo->Lnext, lo);
					if (tempHalfEdge == NULL) return 0;
					lo = tempHalfEdge->Sym;
			}
			lo = lo->Lprev;
		} 
        else 
        {
			/* lo->Org is on the left.  We can make CCW triangles from up->Dst. */
			while (lo->Lnext != up && (EdgeGoesRight(up->Lprev)
				|| EdgeSign(up->Dst, up->pOrigin, up->Lprev->pOrigin) >= 0)) 
            {
                THalfEdge *tempHalfEdge= tessMeshConnect(pMesh, up, up->Lprev);
                if (tempHalfEdge == NULL) return 0;
                up = tempHalfEdge->Sym;
			}
			up = up->Lnext;
		}
	}

	/* Now lo->Org == up->Dst == the leftmost vertex.  The remaining region
	* can be tessellated in a fan from this leftmost vertex.
	*/
	assert(lo->Lnext != up);
	while (lo->Lnext->Lnext != up) 
    {
		THalfEdge *tempHalfEdge= tessMeshConnect(pMesh, lo->Lnext, lo);
		if (tempHalfEdge == NULL) return 0;
		lo = tempHalfEdge->Sym;
	}

	return 1;
}


/* tessMeshTessellateInterior (mesh)  tessellates each region of
* the mesh which is marked "inside" the polygon.  Each such region
* must be monotone.
*/
int tessMeshTessellateInterior(TMesh *pMesh)
{
	TFace *f, *next;

	/*LINTED*/
	for (f = pMesh->fHead.pNext; f != &pMesh->fHead; f = next)
    {
		/* Make sure we don''t try to tessellate the new triangles. */
		next = f->pNext;
		if (f->bInside) 
        {
			if (!tessMeshTessellateMonoRegion(pMesh, f)) return 0;
		}
	}

	return 1;
}


/* tessMeshDiscardExterior (mesh)  zaps (ie. sets to NULL) all faces
* which are not marked "inside" the polygon.  Since further mesh operations
* on NULL faces are not allowed, the main purpose is to clean up the
* mesh so that exterior loops are not represented in the data structure.
*/
void tessMeshDiscardExterior(TMesh *pMesh)
{
	TFace *f, *next;

	/*LINTED*/
	for (f = pMesh->fHead.pNext; f != &pMesh->fHead; f = next) 
    {
		/* Since f will be destroyed, save its next pointer. */
		next = f->pNext;
		if (!f->bInside) 
        {
			tessMeshZapFace(pMesh, f);
		}
	}
}

/* tessMeshSetWindingNumber (mesh, value, keepOnlyBoundary)  resets the
* winding numbers on all edges so that regions marked "inside" the
* polygon have a winding number of "value", and regions outside
* have a winding number of 0.
*
* If keepOnlyBoundary is TRUE, it also deletes all edges which do not
* separate an interior region from an exterior one.
*/
int tessMeshSetWindingNumber (
    TMesh *pMesh, int nValue, int bKeepOnlyBoundary)
{
	THalfEdge *e, *eNext;

	for (e = pMesh->eHead.pNext; e != &pMesh->eHead; e = eNext) 
    {
		eNext = e->pNext;
		if (e->Rface->bInside != e->Lface->bInside) 
        {
			/* This is a boundary edge (one side is interior, one is exterior). */
			e->nWinding = (e->Lface->bInside) ? nValue : -nValue;
		} 
        else 
        {
			/* Both regions are interior, or both are exterior. */
			if (!bKeepOnlyBoundary)
            {
				e->nWinding = 0;
			} 
            else 
            {
				if (!tessMeshDelete(pMesh, e)) return 0;
			}
		}
	}
	return 1;
}

void* heapAlloc(void* userData, unsigned int size)
{
	return malloc(size);
}

void* heapRealloc(void *userData, void* ptr, unsigned int size)
{
	return realloc(ptr, size);
}

void heapFree(void* userData, void* ptr)
{
	free(ptr);
}

static TAlloc defaulAlloc =
{
	heapAlloc,
	heapRealloc,
	heapFree,
	0,
	0,
	0,
	0,
	0,
	0,
	0,
};

TTesselator* tessNewTess(TAlloc* pAlloc)
{
	TTesselator* pTess = NULL;

	if (pAlloc == NULL)
		pAlloc = &defaulAlloc;
	
	/* Only initialize fields which can be changed by the api.  Other fields
	* are initialized where they are used.
	*/

	pTess = (TTesselator *)pAlloc->MemAlloc(pAlloc->pUserData, sizeof(TTesselator));
	if (pTess == NULL) 
    {
		return 0;          /* out of memory */
	}
	pTess->Alloc = *pAlloc;
	/* Check and set defaults. */
	if (pTess->Alloc.nMeshEdgeBucketSize == 0)
		pTess->Alloc.nMeshEdgeBucketSize = 512;
	if (pTess->Alloc.nMeshVertexBucketSize == 0)
		pTess->Alloc.nMeshVertexBucketSize = 512;
	if (pTess->Alloc.nMeshFaceBucketSize == 0)
		pTess->Alloc.nMeshFaceBucketSize = 256;
	if (pTess->Alloc.nDictNodeBucketSize == 0)
		pTess->Alloc.nDictNodeBucketSize = 512;
	if (pTess->Alloc.nRegionBucketSize == 0)
		pTess->Alloc.nRegionBucketSize = 256;
	
	pTess->fNormal[0] = 0;
	pTess->fNormal[1] = 0;
	pTess->fNormal[2] = 0;

	pTess->fBMin[0] = 0;
	pTess->fBMin[1] = 0;
	pTess->fBMax[0] = 0;
	pTess->fBMax[1] = 0;

	pTess->nWindingRule = TESS_WINDING_ODD;

	if (pTess->Alloc.nRegionBucketSize < 16)
		pTess->Alloc.nRegionBucketSize = 16;
	if (pTess->Alloc.nRegionBucketSize > 4096)
		pTess->Alloc.nRegionBucketSize = 4096;
	pTess->pRegionPool = CreateBucketAlloc (
        &pTess->Alloc, "Regions", sizeof(TActiveRegion), pTess->Alloc.nRegionBucketSize);

	// Initialize to begin polygon.
	pTess->pMesh = NULL;

	pTess->nOutOfMemory = 0;
	pTess->nVertexIndexCounter = 0;
	
	pTess->pVertices = 0;
	pTess->pVertexIndices = 0;
	pTess->nVertexCount = 0;
	pTess->pElements = 0;
	pTess->nElementCount = 0;

	return pTess;
}

void tessDeleteTess(TTesselator *pTess)
{	
	struct TAlloc Alloc = pTess->Alloc;
	
	DeleteBucketAlloc(pTess->pRegionPool);

	if (pTess->pMesh != NULL) 
    {
		tessMeshDeleteMesh(&Alloc, pTess->pMesh);
		pTess->pMesh = NULL;
	}
	if (pTess->pVertices != NULL) 
    {
		Alloc.MemFree(Alloc.pUserData, pTess->pVertices);
		pTess->pVertices = 0;
	}
	if (pTess->pVertexIndices != NULL) 
    {
		Alloc.MemFree(Alloc.pUserData, pTess->pVertexIndices);
		pTess->pVertexIndices = 0;
	}
	if (pTess->pElements != NULL) 
    {
		Alloc.MemFree(Alloc.pUserData, pTess->pElements);
		pTess->pElements = 0;
	}

	Alloc.MemFree(Alloc.pUserData, pTess);
}


static int GetNeighbourFace(THalfEdge* pEdge)
{
	if (!pEdge->Rface)
		return TESS_UNDEF;
	if (!pEdge->Rface->bInside)
		return TESS_UNDEF;
	return pEdge->Rface->n;
}

void OutputPolymesh(TTesselator* pTess, TMesh* pMesh, 
                    int nElementType, int nPolySize, int nVertexSize)
{
	TVertex* pVertex = 0;
	TFace* pFace = 0;
	THalfEdge* pHalfEdge = 0;
	int nMaxFaceCount = 0;
	int nMaxVertexCount = 0;
	int nFaceVerts, nI;
	int *pElements = 0;
	float *fVert;

	// Assume that the input data is triangles now.
	// Try to merge as many polygons as possible
	if (nPolySize > 3)
	{
		if (!tessMeshMergeConvexFaces(pMesh, nPolySize))
		{
			pTess->nOutOfMemory = 1;
			return;
		}
	}

	// Mark unused
	for (pVertex = pMesh->vHead.pNext; pVertex != &pMesh->vHead; pVertex = pVertex->pNext)
		pVertex->n = TESS_UNDEF;

	// Create unique IDs for all vertices and faces.
	for (pFace = pMesh->fHead.pNext; pFace != &pMesh->fHead; pFace = pFace->pNext)
	{
		pFace->n = TESS_UNDEF;
		if (!pFace->bInside) continue;

		pHalfEdge = pFace->pHalfEdge;
		nFaceVerts = 0;
		do
		{
			pVertex = pHalfEdge->pOrigin;
			if (pVertex->n == TESS_UNDEF)
			{
				pVertex->n = nMaxVertexCount;
				nMaxVertexCount++;
			}
			nFaceVerts++;
			pHalfEdge = pHalfEdge->Lnext;
		}
		while (pHalfEdge != pFace->pHalfEdge);
		
		assert(nFaceVerts <= nPolySize);

		pFace->n = nMaxFaceCount;
		++nMaxFaceCount;
	}

	pTess->nElementCount = nMaxFaceCount;
	if (nElementType == TESS_CONNECTED_POLYGONS)
		nMaxFaceCount *= 2;
	pTess->pElements = (int*)pTess->Alloc.MemAlloc(
        pTess->Alloc.pUserData, sizeof(int) * nMaxFaceCount * nPolySize);
	if (!pTess->pElements)
	{
		pTess->nOutOfMemory = 1;
		return;
	}
	
	pTess->nVertexCount = nMaxVertexCount;
	pTess->pVertices = (float*)pTess->Alloc.MemAlloc(
        pTess->Alloc.pUserData, sizeof(float) * pTess->nVertexCount * nVertexSize);
	if (!pTess->pVertices)
	{
		pTess->nOutOfMemory = 1;
		return;
	}

	pTess->pVertexIndices = (int*)pTess->Alloc.MemAlloc(
        pTess->Alloc.pUserData, sizeof(int) * pTess->nVertexCount);
	if (!pTess->pVertexIndices)
	{
		pTess->nOutOfMemory = 1;
		return;
	}
	
	// Output vertices.
	for (pVertex = pMesh->vHead.pNext; pVertex != &pMesh->vHead; pVertex = pVertex->pNext)
	{
		if (pVertex->n != TESS_UNDEF)
		{
			// Store coordinate
			fVert = &pTess->pVertices[pVertex->n*nVertexSize];
			fVert[0] = pVertex->fCoords[0];
			fVert[1] = pVertex->fCoords[1];
			if (nVertexSize > 2)
				fVert[2] = pVertex->fCoords[2];
			// Store vertex index.
			pTess->pVertexIndices[pVertex->n] = pVertex->idx;
		}
	}

	// Output indices.
	pElements = pTess->pElements;
	for (pFace = pMesh->fHead.pNext; pFace != &pMesh->fHead; pFace = pFace->pNext)
	{
		if (!pFace->bInside) continue;
		
		// Store polygon
		pHalfEdge = pFace->pHalfEdge;
		nFaceVerts = 0;
		do
		{
			pVertex = pHalfEdge->pOrigin;
			*pElements++ = pVertex->n;
			nFaceVerts++;
			pHalfEdge = pHalfEdge->Lnext;
		}
		while (pHalfEdge != pFace->pHalfEdge);
		// Fill unused.
		for (nI = nFaceVerts; nI < nPolySize; ++nI)
			*pElements++ = TESS_UNDEF;

		// Store polygon connectivity
		if (nElementType == TESS_CONNECTED_POLYGONS)
		{
			pHalfEdge = pFace->pHalfEdge;
			do
			{
				*pElements++ = GetNeighbourFace (pHalfEdge) ;
				pHalfEdge = pHalfEdge->Lnext;
			}
			while (pHalfEdge != pFace->pHalfEdge);
			// Fill unused.
			for (nI = nFaceVerts; nI < nPolySize; ++nI)
				*pElements++ = TESS_UNDEF;
		}
	}
}

void OutputContours(TTesselator *pTess, TMesh *pMesh, int nVertexSize)
{
	TFace *pFace = 0;
	THalfEdge *pEdge = 0;
	THalfEdge *pStart = 0;
	float *pVerts = 0;
	int *pElements = 0;
	int *pVertInds = 0;
	int nStartVert = 0;
	int nVertCount = 0;

	pTess->nVertexCount = 0;
	pTess->nElementCount = 0;

	for (pFace = pMesh->fHead.pNext; pFace != &pMesh->fHead; pFace = pFace->pNext)
	{
		if (!pFace->bInside) continue;

		pStart = pEdge = pFace->pHalfEdge;
		do
		{
			++pTess->nVertexCount;
			pEdge = pEdge->Lnext;
		}
		while (pEdge != pStart);

		++pTess->nElementCount;
	}

	pTess->pElements = (int*)pTess->Alloc.MemAlloc (
        pTess->Alloc.pUserData, sizeof(int) * pTess->nElementCount * 2);
	if (!pTess->pElements)
	{
		pTess->nOutOfMemory = 1;
		return;
	}
	
	pTess->pVertices = (float*)pTess->Alloc.MemAlloc(
        pTess->Alloc.pUserData, sizeof(float) * pTess->nVertexCount * nVertexSize);
    if (!pTess->pVertices)
	{
		pTess->nOutOfMemory = 1;
		return;
	}

	pTess->pVertexIndices = (int*)pTess->Alloc.MemAlloc (
        pTess->Alloc.pUserData, sizeof(int) * pTess->nVertexCount);
    if (!pTess->pVertexIndices)
	{
		pTess->nOutOfMemory = 1;
		return;
	}
	
	pVerts = pTess->pVertices;
	pElements = pTess->pElements;
	pVertInds = pTess->pVertexIndices;

	nStartVert = 0;

	for (pFace = pMesh->fHead.pNext; pFace != &pMesh->fHead; pFace = pFace->pNext)
	{
		if (!pFace->bInside) continue;

		nVertCount = 0;
		pStart = pEdge = pFace->pHalfEdge;
		do
		{
			*pVerts++ = pEdge->pOrigin->fCoords[0];
			*pVerts++ = pEdge->pOrigin->fCoords[1];
			if (nVertexSize > 2)
				*pVerts++ = pEdge->pOrigin->fCoords[2];
			*pVertInds++ = pEdge->pOrigin->idx;
			++nVertCount;
			pEdge = pEdge->Lnext;
		}
		while (pEdge != pStart);

		pElements[0] = nStartVert;
		pElements[1] = nVertCount;
		pElements += 2;

		nStartVert += nVertCount;
	}
}

void tessAddContour(TTesselator *pTess, int nSize, const void* pVertices,
					int nStride, int nNumVertices)
{
	const unsigned char *src = (const unsigned char*)pVertices;
	THalfEdge *pEdge;
	int i;

	if (pTess->pMesh == NULL)
	  	pTess->pMesh = tessMeshNewMesh(&pTess->Alloc);
 	if (pTess->pMesh == NULL)
    {
		pTess->nOutOfMemory = 1;
		return;
	}

	if (nSize < 2)
		nSize = 2;
	if (nSize > 3)
		nSize = 3;

	pEdge = NULL;

	for (i = 0; i < nNumVertices; ++i)
	{
		const float* coords = (const float*)src;
		src += nStride;

		if (pEdge == NULL) 
        {
			/* Make a self-loop (one vertex, one edge). */
			pEdge = tessMeshMakeEdge(pTess->pMesh);
			if (pEdge == NULL) 
            {
				pTess->nOutOfMemory = 1;
				return;
			}
			if (!tessMeshSplice(pTess->pMesh, pEdge, pEdge->Sym)) 
            {
				pTess->nOutOfMemory = 1;
				return;
			}
		} 
        else 
        {
			/* Create a new vertex and edge which immediately follow e
			* in the ordering around the left face.
			*/
			if (tessMeshSplitEdge(pTess->pMesh, pEdge) == NULL) 
            {
				pTess->nOutOfMemory = 1;
				return;
			}
			pEdge = pEdge->Lnext;
		}

		/* The new vertex is now e->Org. */
		pEdge->pOrigin->fCoords[0] = coords[0];
		pEdge->pOrigin->fCoords[1] = coords[1];
		if (nSize > 2)
			pEdge->pOrigin->fCoords[2] = coords[2];
		else
			pEdge->pOrigin->fCoords[2] = 0;
		/* Store the insertion number so that the vertex can be later recognized. */
		pEdge->pOrigin->idx = pTess->nVertexIndexCounter++;

		/* The winding of an edge says how the winding number changes as we
		* cross from the edge''s right face to its left face.  We add the
		* vertices in such an order that a CCW contour will add +1 to
		* the winding number of the region inside the contour.
		*/
		pEdge->nWinding = 1;
		pEdge->Sym->nWinding = -1;
	}
}

int tessTesselate(TTesselator *pTess, int nWindingRule, int nElementType,
				  int nPolySize, int nVertexSize, const float* fNormal)
{
	TMesh *pMesh;
	int rc = 1;

	if (pTess->pVertices != NULL) 
    {
		pTess->Alloc.MemFree(pTess->Alloc.pUserData, pTess->pVertices);
		pTess->pVertices = 0;
	}
	if (pTess->pElements != NULL) 
    {
		pTess->Alloc.MemFree(pTess->Alloc.pUserData, pTess->pElements);
		pTess->pElements = 0;
	}
	if (pTess->pVertexIndices != NULL) 
    {
		pTess->Alloc.MemFree(pTess->Alloc.pUserData, pTess->pVertexIndices);
		pTess->pVertexIndices = 0;
	}

	pTess->nVertexIndexCounter = 0;
	
	if (fNormal)
	{
		pTess->fNormal[0] = fNormal[0];
		pTess->fNormal[1] = fNormal[1];
		pTess->fNormal[2] = fNormal[2];
	}

	pTess->nWindingRule = nWindingRule;

	if (nVertexSize < 2)
		nVertexSize = 2;
	if (nVertexSize > 3)
		nVertexSize = 3;

	if (setjmp(pTess->env) != 0) 
    { 
		/* come back here if out of memory */
		return 0;
	}

	if (!pTess->pMesh)
	{
		return 0;
	}

	/* Determine the polygon normal and project vertices onto the plane
	* of the polygon.
	*/
	tessProjectPolygon(pTess);

	/* tessComputeInterior (tess)  computes the planar arrangement specified
	* by the given contours, and further subdivides this arrangement
	* into regions.  Each region is marked "inside" if it belongs
	* to the polygon, according to the rule given by tess->windingRule.
	* Each interior region is guaranteed be monotone.
	*/
	if (!tessComputeInterior(pTess)) 
    {
		longjmp(pTess->env,1);  /* could've used a label */
	}

	pMesh = pTess->pMesh;

	/* If the user wants only the boundary contours, we throw away all edges
	* except those which separate the interior from the exterior.
	* Otherwise we tessellate all the regions marked "inside".
	*/
	if (nElementType == TESS_BOUNDARY_CONTOURS) 
    {
		rc = tessMeshSetWindingNumber(pMesh, 1, TRUE);
	} 
    else 
    {
		rc = tessMeshTessellateInterior(pMesh); 
	}
	if (rc == 0) longjmp(pTess->env, 1);  /* could've used a label */

	tessMeshCheckMesh(pMesh);

	if (nElementType == TESS_BOUNDARY_CONTOURS) 
    {
		OutputContours(pTess, pMesh, nVertexSize);     /* output contours */
	}
	else
	{
		OutputPolymesh(pTess, pMesh, nElementType, nPolySize, nVertexSize);     /* output polygons */
	}

	tessMeshDeleteMesh(&pTess->Alloc, pMesh);
	pTess->pMesh = NULL;

	if (pTess->nOutOfMemory)
		return 0;
	return 1;
}

int tessGetVertexCount(TTesselator *pTess)
{
	return pTess->nVertexCount;
}

const float* tessGetVertices(TTesselator *pTess)
{
	return pTess->pVertices;
}

const int* tessGetVertexIndices(TTesselator *pTess)
{
	return pTess->pVertexIndices;
}

int tessGetElementCount(TTesselator *pTess)
{
	return pTess->nElementCount;
}

const int* tessGetElements(TTesselator *pTess)
{
	return pTess->pElements;
}
