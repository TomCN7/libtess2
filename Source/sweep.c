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

#include <assert.h>
#include <stddef.h>
#include <setjmp.h>		/* longjmp */

#include "mesh.h"
#include "geom.h"
#include "tess.h"
#include "dict.h"
#include "priorityq.h"
#include "bucketalloc.h"
#include "sweep.h"

#define true 1
#define false 0

#ifdef FOR_TRITE_TEST_PROGRAM
extern void DebugEvent (TTesselator *tess) ;
#else
#define DebugEvent(tess)
#endif

/*
* Invariants for the Edge Dictionary.
* - each pair of adjacent edges e2=Succ(e1) satisfies EdgeLeq(e1,e2)
*   at any valid location of the sweep event
* - if EdgeLeq(e2,e1) as well (at any valid sweep event), then e1 and e2
*   share a common endpoint
* - for each e, e->Dst has been processed, but not e->Org
* - each edge e satisfies VertLeq(e->Dst,event) && VertLeq(event,e->Org)
*   where "event" is the current sweep line event.
* - no edge e has zero length
*
* Invariants for the Mesh (the processed portion).
* - the portion of the mesh left of the sweep line is a planar graph,
*   ie. there is *some* way to embed it in the plane
* - no processed edge has zero length
* - no two processed vertices have identical coordinates
* - each "inside" region is monotone, ie. can be broken into two chains
*   of monotonically increasing vertices according to VertLeq(v1,v2)
*   - a non-invariant: these chains may intersect (very slightly)
*
* Invariants for the Sweep.
* - if none of the edges incident to the event vertex have an activeRegion
*   (ie. none of these edges are in the edge dictionary), then the vertex
*   has only right-going edges.
* - if an edge is marked "fixUpperEdge" (it is a temporary edge introduced
*   by ConnectRightVertex), then it is the only right-going edge from
*   its associated vertex.  (This says that these edges exist only
*   when it is necessary.)
*/

#define MAX(x,y)	((x) >= (y) ? (x) : (y))
#define MIN(x,y)	((x) <= (y) ? (x) : (y))

/* When we merge two edges into one, we need to compute the combined
* winding of the new edge.
*/
#define AddWinding(eDst,eSrc)	(eDst->nWinding += eSrc->nWinding, \
	eDst->Sym->nWinding += eSrc->Sym->nWinding)

static void SweepEvent(TTesselator *pTess, TVertex *pVEvent);
static void WalkDirtyRegions(TTesselator *pTess, TActiveRegion *pRegUp);
static int CheckForRightSplice(TTesselator *pTess, TActiveRegion *pRegUp);

/*
* Both edges must be directed from right to left (this is the canonical
* direction for the upper edge of each region).
*
* The strategy is to evaluate a "t" value for each edge at the
* current sweep line position, given by tess->event.  The calculations
* are designed to be very stable, but of course they are not perfect.
*
* Special case: if both edge destinations are at the sweep event,
* we sort the edges by slope (they would otherwise compare equally).
*/
static int EdgeLeq(TTesselator *pTess, TActiveRegion *pReg1, TActiveRegion *pReg2) 
{
	TVertex *pVEvent = pTess->pVEvent;
	THalfEdge *pEdge1 = NULL, *pEdge2 = NULL;
	float t1, t2;

	pEdge1 = pReg1->pEdgeUp;
	pEdge2 = pReg2->pEdgeUp;

	if (pEdge1->Dst == pVEvent)  
	{
		if (pEdge2->Dst == pVEvent)  
        {
			/* Two edges right of the sweep line which meet at the sweep event.
			* Sort them by slope.
			*/
			if (VertLeq(pEdge1->pOrigin, pEdge2->pOrigin)) 
            {
				return EdgeSign(pEdge2->Dst, pEdge1->pOrigin, pEdge2->pOrigin) <= 0;
			}
			return EdgeSign(pEdge1->Dst, pEdge2->pOrigin, pEdge1->pOrigin) >= 0;
		}
		return EdgeSign(pEdge2->Dst, pVEvent, pEdge2->pOrigin) <= 0;
	}
	if (pEdge2->Dst == pVEvent)  
 	{
		return EdgeSign(pEdge1->Dst, pVEvent, pEdge1->pOrigin) >= 0;
	}

	/* General case - compute signed distance *from* e1, e2 to event */
	t1 = EdgeEval(pEdge1->Dst, pVEvent, pEdge1->pOrigin);
	t2 = EdgeEval(pEdge2->Dst, pVEvent, pEdge2->pOrigin);
	return (t1 >= t2);
}


static void DeleteRegion(TTesselator *pTess, TActiveRegion *pRegion)
{
	if (pRegion->bFixUpperEdge) 
	{
		/* It was created with zero winding number, so it better be
		* deleted with zero winding number (ie. it better not get merged
		* with a real edge).
		*/
		assert(pRegion->pEdgeUp->nWinding == 0);
	}
	pRegion->pEdgeUp->pActiveRegion = NULL;
	dictDelete(pTess->pDict, pRegion->pNodeUp);
	BucketFree(pTess->pRegionPool, pRegion);
}

/*
* Replace an upper edge which needs fixing (see ConnectRightVertex).
*/
static int FixUpperEdge(TTesselator *pTess, TActiveRegion *pRegion, THalfEdge *pNewEdge)
{
	assert(pRegion->bFixUpperEdge);
	if (!tessMeshDelete(pTess->pMesh, pRegion->pEdgeUp)) return 0;
	pRegion->bFixUpperEdge = false;
	pRegion->pEdgeUp = pNewEdge;
	pNewEdge->pActiveRegion = pRegion;

	return 1; 
}

static TActiveRegion *TopLeftRegion(TTesselator *pTess, TActiveRegion *pRegion)
{
	TVertex *pOrigion = pRegion->pEdgeUp->pOrigin;
	THalfEdge *pEdge = NULL;

	/* Find the region above the uppermost edge with the same origin */
	do 
	{
		pRegion = RegionAbove(pRegion);
	} while (pRegion->pEdgeUp->pOrigin == pOrigion);

	/* If the edge above was a temporary edge introduced by ConnectRightVertex,
	* now is the time to fix it.
	*/
	if (pRegion->bFixUpperEdge) 
    {
		pEdge = tessMeshConnect(pTess->pMesh, RegionBelow(pRegion)->pEdgeUp->Sym, pRegion->pEdgeUp->Lnext);
		if (pEdge == NULL) return NULL;
		if (!FixUpperEdge(pTess, pRegion, pEdge)) return NULL;
		pRegion = RegionAbove(pRegion);
	}
	return pRegion;
}

static TActiveRegion *TopRightRegion(TActiveRegion *pRegion)
{
	TVertex *pDst = pRegion->pEdgeUp->Dst;

	/* Find the region above the uppermost edge with the same destination */
	do 
    {
		pRegion = RegionAbove(pRegion);
	} while (pRegion->pEdgeUp->Dst == pDst);

    return pRegion;
}

/*
* Add a new active region to the sweep line, *somewhere* below "regAbove"
* (according to where the new edge belongs in the sweep-line dictionary).
* The upper edge of the new region will be "eNewUp".
* Winding number and "inside" flag are not updated.
*/
static TActiveRegion *AddRegionBelow(
    TTesselator *pTess, TActiveRegion *pRegAbove, THalfEdge *pEdgeNewUp)
{
	TActiveRegion *pRegNew = (TActiveRegion *)BucketAlloc(pTess->pRegionPool);
	if (pRegNew == NULL) longjmp(pTess->env,1);

	pRegNew->pEdgeUp = pEdgeNewUp;
	pRegNew->pNodeUp = dictInsertBefore(pTess->pDict, pRegAbove->pNodeUp, pRegNew);
	if (pRegNew->pNodeUp == NULL) longjmp(pTess->env,1);
	pRegNew->bFixUpperEdge = false;
	pRegNew->bSentinel = false;
	pRegNew->bDirty = false;

	pEdgeNewUp->pActiveRegion = pRegNew;
	return pRegNew;
}

static int IsWindingInside(TTesselator *pTess, int n)
{
	switch (pTess->nWindingRule) 
    {
		case TESS_WINDING_ODD:
			return (n & 1);
		case TESS_WINDING_NONZERO:
			return (n != 0);
		case TESS_WINDING_POSITIVE:
			return (n > 0);
		case TESS_WINDING_NEGATIVE:
			return (n < 0);
		case TESS_WINDING_ABS_GEQ_TWO:
			return (n >= 2) || (n <= -2);
	}
	/*LINTED*/
	assert (false);
	/*NOTREACHED*/

	return (false);
}


static void ComputeWinding(TTesselator *pTess, TActiveRegion *pRegion)
{
	pRegion->nWindingNumber = RegionAbove(pRegion)->nWindingNumber + pRegion->pEdgeUp->nWinding;
	pRegion->bInside = IsWindingInside(pTess, pRegion->nWindingNumber);
}


/*
* Delete a region from the sweep line.  This happens when the upper
* and lower chains of a region meet (at a vertex on the sweep line).
* The "inside" flag is copied to the appropriate mesh face (we could
* not do this before -- since the structure of the mesh is always
* changing, this face may not have even existed until now).
*/
static void FinishRegion(TTesselator *pTess, TActiveRegion *pRegion)
{
	THalfEdge *pEdge = pRegion->pEdgeUp;
	TFace *pFace = pEdge->Lface;

	pFace->bInside = pRegion->bInside;
	pFace->pHalfEdge = pEdge;   /* optimization for tessMeshTessellateMonoRegion() */
	DeleteRegion(pTess, pRegion);
}


/*
* We are given a vertex with one or more left-going edges.  All affected
* edges should be in the edge dictionary.  Starting at regFirst->eUp,
* we walk down deleting all regions where both edges have the same
* origin vOrg.  At the same time we copy the "inside" flag from the
* active region to the face, since at this point each face will belong
* to at most one region (this was not necessarily true until this point
* in the sweep).  The walk stops at the region above regLast; if regLast
* is NULL we walk as far as possible.  At the same time we relink the
* mesh if necessary, so that the ordering of edges around vOrg is the
* same as in the dictionary.
*/
static THalfEdge *FinishLeftRegions(
    TTesselator *pTess, TActiveRegion *pRegFirst, TActiveRegion *pRegLast)
{
	TActiveRegion *pReg = NULL, *pRegPrev = NULL;
	THalfEdge *pEdge = NULL, *pEdgePrev = NULL;

	pRegPrev = pRegFirst;
	pEdgePrev = pRegFirst->pEdgeUp;
	while (pRegPrev != pRegLast) 
    {
		pRegPrev->bFixUpperEdge = false;	/* placement was OK */
		pReg = RegionBelow(pRegPrev);
		pEdge = pReg->pEdgeUp;
		if (pEdge->pOrigin != pEdgePrev->pOrigin) 
        {
			if (!pReg->bFixUpperEdge)
            {
				/* Remove the last left-going edge.  Even though there are no further
				* edges in the dictionary with this origin, there may be further
				* such edges in the mesh (if we are adding left edges to a vertex
				* that has already been processed).  Thus it is important to call
				* FinishRegion rather than just DeleteRegion.
				*/
				FinishRegion(pTess, pRegPrev);
				break;
			}
			/* If the edge below was a temporary edge introduced by
			* ConnectRightVertex, now is the time to fix it.
			*/
			pEdge = tessMeshConnect(pTess->pMesh, pEdgePrev->Lprev, pEdge->Sym);
			if (pEdge == NULL) longjmp(pTess->env,1);
			if (!FixUpperEdge(pTess, pReg, pEdge)) longjmp(pTess->env,1);
		}

		/* Relink edges so that ePrev->Onext == e */
		if (pEdgePrev->Onext != pEdge)
        {
			if (!tessMeshSplice(pTess->pMesh, pEdge->Oprev, pEdge)) longjmp(pTess->env,1);
			if (!tessMeshSplice(pTess->pMesh, pEdgePrev, pEdge)) longjmp(pTess->env,1);
		}
		FinishRegion(pTess, pRegPrev);	/* may change reg->eUp */
		pEdgePrev = pReg->pEdgeUp;
		pRegPrev = pReg;
	}

	return pEdgePrev;
}


/*
* Purpose: insert right-going edges into the edge dictionary, and update
* winding numbers and mesh connectivity appropriately.  All right-going
* edges share a common origin vOrg.  Edges are inserted CCW starting at
* eFirst; the last edge inserted is eLast->Oprev.  If vOrg has any
* left-going edges already processed, then eTopLeft must be the edge
* such that an imaginary upward vertical segment from vOrg would be
* contained between eTopLeft->Oprev and eTopLeft; otherwise eTopLeft
* should be NULL.
*/
static void AddRightEdges (
    TTesselator *pTess, TActiveRegion *pRegUp,
    THalfEdge *pEdgeFirst, THalfEdge *pEdgeLast, THalfEdge *pEdgeTopLeft, int bCleanUp) 
{
	TActiveRegion *pReg = NULL, *pRegPrev = NULL;
	THalfEdge *pEdge = NULL, *pEdgePrev = NULL;
	int bFirstTime = true;

	/* Insert the new right-going edges in the dictionary */
	pEdge = pEdgeFirst;
	do 
    {
		assert(VertLeq(pEdge->pOrigin, pEdge->Dst));
		AddRegionBelow(pTess, pRegUp, pEdge->Sym);
		pEdge = pEdge->Onext;
	} while (pEdge != pEdgeLast);

	/* Walk *all* right-going edges from e->Org, in the dictionary order,
	* updating the winding numbers of each region, and re-linking the mesh
	* edges to match the dictionary ordering (if necessary).
	*/
	if (pEdgeTopLeft == NULL)  
    {
		pEdgeTopLeft = RegionBelow(pRegUp)->pEdgeUp->Rprev;
	}
	pRegPrev = pRegUp;
	pEdgePrev = pEdgeTopLeft;
	for (;;)
    {
		pReg = RegionBelow(pRegPrev);
		pEdge = pReg->pEdgeUp->Sym;
		if (pEdge->pOrigin != pEdgePrev->pOrigin)  break;

		if (pEdge->Onext != pEdgePrev)  
        {
			/* Unlink e from its current position, and relink below ePrev */
			if (!tessMeshSplice(pTess->pMesh, pEdge->Oprev, pEdge))  longjmp(pTess->env,1);
			if (!tessMeshSplice(pTess->pMesh, pEdgePrev->Oprev, pEdge))  longjmp(pTess->env,1);
		}
		/* Compute the winding number and "inside" flag for the new regions */
		pReg->nWindingNumber = pRegPrev->nWindingNumber - pEdge->nWinding;
		pReg->bInside = IsWindingInside(pTess, pReg->nWindingNumber);

		/* Check for two outgoing edges with same slope -- process these
		* before any intersection tests (see example in tessComputeInterior).
		*/
		pRegPrev->bDirty = true;
		if (!bFirstTime && CheckForRightSplice(pTess, pRegPrev)) 
        {
			AddWinding(pEdge, pEdgePrev);
			DeleteRegion(pTess, pRegPrev);
			if (!tessMeshDelete(pTess->pMesh, pEdgePrev)) longjmp(pTess->env,1);
		}
		bFirstTime = false;
		pRegPrev = pReg;
		pEdgePrev = pEdge;
	}
	pRegPrev->bDirty = true;
	assert(pRegPrev->nWindingNumber - pEdge->nWinding == pReg->nWindingNumber);

	if (bCleanUp)  
	{
		/* Check for intersections between newly adjacent edges. */
		WalkDirtyRegions(pTess, pRegPrev);
	}
}

/*
* Two vertices with idential coordinates are combined into one.
* e1->Org is kept, while e2->Org is discarded.
*/
static void SpliceMergeVertices (
    TTesselator *pTess, THalfEdge *pEdge1, THalfEdge *pEdge2) 
{
	if (!tessMeshSplice(pTess->pMesh, pEdge1, pEdge2)) longjmp(pTess->env,1); 
}

/*
* Find some weights which describe how the intersection vertex is
* a linear combination of "org" and "dest".  Each of the two edges
* which generated "isect" is allocated 50% of the weight; each edge
* splits the weight between its org and dst according to the
* relative distance to "isect".
*/
static void VertexWeights (
    TVertex *pVIntersect, TVertex *pVOrg, TVertex *pVDst, float *fWeights) 
{
	float t1 = VertL1dist(pVOrg, pVIntersect);
	float t2 = VertL1dist(pVDst, pVIntersect);

	fWeights[0] = (float)0.5 * t2 / (t1 + t2);
	fWeights[1] = (float)0.5 * t1 / (t1 + t2);
	pVIntersect->fCoords[0] += fWeights[0]*pVOrg->fCoords[0] + fWeights[1]*pVDst->fCoords[0];
	pVIntersect->fCoords[1] += fWeights[0]*pVOrg->fCoords[1] + fWeights[1]*pVDst->fCoords[1];
	pVIntersect->fCoords[2] += fWeights[0]*pVOrg->fCoords[2] + fWeights[1]*pVDst->fCoords[2];
}

 /*
 * We've computed a new intersection point, now we need a "data" pointer
 * from the user so that we can refer to this new vertex in the
 * rendering callbacks.
 */
static void GetIntersectData (TTesselator *pTess, TVertex *pVIntersect,
    TVertex *pVOrgUp, TVertex *pVDstUp, TVertex *pVOrgLo, TVertex *pVDstLo) 
{
	float weights[4];

	pVIntersect->fCoords[0] = pVIntersect->fCoords[1] = pVIntersect->fCoords[2] = 0;
	pVIntersect->idx = TESS_UNDEF;
	VertexWeights(pVIntersect, pVOrgUp, pVDstUp, &weights[0]);
	VertexWeights(pVIntersect, pVOrgLo, pVDstLo, &weights[2]);
}

/*
* Check the upper and lower edge of "regUp", to make sure that the
* eUp->Org is above eLo, or eLo->Org is below eUp (depending on which
* origin is leftmost).
*
* The main purpose is to splice right-going edges with the same
* dest vertex and nearly identical slopes (ie. we can't distinguish
* the slopes numerically).  However the splicing can also help us
* to recover from numerical errors.  For example, suppose at one
* point we checked eUp and eLo, and decided that eUp->Org is barely
* above eLo.  Then later, we split eLo into two edges (eg. from
* a splice operation like this one).  This can change the result of
* our test so that now eUp->Org is incident to eLo, or barely below it.
* We must correct this condition to maintain the dictionary invariants.
*
* One possibility is to check these edges for intersection again
* (ie. CheckForIntersect).  This is what we do if possible.  However
* CheckForIntersect requires that tess->event lies between eUp and eLo,
* so that it has something to fall back on when the intersection
* calculation gives us an unusable answer.  So, for those cases where
* we can't check for intersection, this routine fixes the problem
* by just splicing the offending vertex into the other edge.
* This is a guaranteed solution, no matter how degenerate things get.
* Basically this is a combinatorial solution to a numerical problem.
*/
static int CheckForRightSplice(TTesselator *pTess, TActiveRegion *pRegUp)
{
	TActiveRegion *pRegLo = RegionBelow(pRegUp);
	THalfEdge *pEdgeUp = pRegUp->pEdgeUp;
	THalfEdge *pEdgeLo = pRegLo->pEdgeUp;

	if (VertLeq(pEdgeUp->pOrigin, pEdgeLo->pOrigin))
    {
		if (EdgeSign(pEdgeLo->Dst, pEdgeUp->pOrigin, pEdgeLo->pOrigin) > 0)  return false;

		/* eUp->Org appears to be below eLo */
		if (!VertEq(pEdgeUp->pOrigin, pEdgeLo->pOrigin))
        {
			/* Splice eUp->Org into eLo */
			if (tessMeshSplitEdge (pTess->pMesh, pEdgeLo->Sym)  == NULL) longjmp(pTess->env,1);
			if (!tessMeshSplice (pTess->pMesh, pEdgeUp, pEdgeLo->Oprev)) longjmp(pTess->env,1);
			pRegUp->bDirty = pRegLo->bDirty = true;
		} 
        else if (pEdgeUp->pOrigin != pEdgeLo->pOrigin) 
        {
			/* merge the two vertices, discarding eUp->Org */
			pqDelete (pTess->pq, pEdgeUp->pOrigin->pqHandle) ;
			SpliceMergeVertices (pTess, pEdgeLo->Oprev, pEdgeUp) ;
		}
	} 
    else 
    {
		if (EdgeSign(pEdgeUp->Dst, pEdgeLo->pOrigin, pEdgeUp->pOrigin) < 0)  return false;

		/* eLo->Org appears to be above eUp, so splice eLo->Org into eUp */
		RegionAbove(pRegUp)->bDirty = pRegUp->bDirty = true;
		if (tessMeshSplitEdge(pTess->pMesh, pEdgeUp->Sym) == NULL) longjmp(pTess->env,1);
		if (!tessMeshSplice(pTess->pMesh, pEdgeLo->Oprev, pEdgeUp)) longjmp(pTess->env,1);
	}
	return true;
}

/*
* Check the upper and lower edge of "regUp", to make sure that the
* eUp->Dst is above eLo, or eLo->Dst is below eUp (depending on which
* destination is rightmost).
*
* Theoretically, this should always be true.  However, splitting an edge
* into two pieces can change the results of previous tests.  For example,
* suppose at one point we checked eUp and eLo, and decided that eUp->Dst
* is barely above eLo.  Then later, we split eLo into two edges (eg. from
* a splice operation like this one).  This can change the result of
* the test so that now eUp->Dst is incident to eLo, or barely below it.
* We must correct this condition to maintain the dictionary invariants
* (otherwise new edges might get inserted in the wrong place in the
* dictionary, and bad stuff will happen).
*
* We fix the problem by just splicing the offending vertex into the
* other edge.
*/
static int CheckForLeftSplice(TTesselator *pTess, TActiveRegion *pRegUp)
{
	TActiveRegion *pRegLo = RegionBelow(pRegUp);
	THalfEdge *pEdgeUp = pRegUp->pEdgeUp;
	THalfEdge *pEdgeLo = pRegLo->pEdgeUp;
	THalfEdge *pEdge = NULL;

	assert(!VertEq(pEdgeUp->Dst, pEdgeLo->Dst));

	if (VertLeq(pEdgeUp->Dst, pEdgeLo->Dst)) 
    {
		if (EdgeSign(pEdgeUp->Dst, pEdgeLo->Dst, pEdgeUp->pOrigin) < 0) return false;

		/* eLo->Dst is above eUp, so splice eLo->Dst into eUp */
		RegionAbove(pRegUp)->bDirty = pRegUp->bDirty = true;
		pEdge = tessMeshSplitEdge(pTess->pMesh, pEdgeUp);
		if (pEdge == NULL) longjmp(pTess->env,1);
		if (!tessMeshSplice(pTess->pMesh, pEdgeLo->Sym, pEdge)) longjmp(pTess->env,1);
		pEdge->Lface->bInside = pRegUp->bInside;
	} 
    else 
    {
		if (EdgeSign(pEdgeLo->Dst, pEdgeUp->Dst, pEdgeLo->pOrigin) > 0)  return false;

		/* eUp->Dst is below eLo, so splice eUp->Dst into eLo */
		pRegUp->bDirty = pRegLo->bDirty = true;
		pEdge = tessMeshSplitEdge(pTess->pMesh, pEdgeLo);
		if (pEdge == NULL) longjmp(pTess->env,1);    
		if (!tessMeshSplice(pTess->pMesh, pEdgeUp->Lnext, pEdgeLo->Sym)) longjmp(pTess->env,1);
		pEdge->Rface->bInside = pRegUp->bInside;
	}

	return true;
}


/*
* Check the upper and lower edges of the given region to see if
* they intersect.  If so, create the intersection and add it
* to the data structures.
*
* Returns true if adding the new intersection resulted in a recursive
* call to AddRightEdges(); in this case all "dirty" regions have been
* checked for intersections, and possibly regUp has been deleted.
*/
static int CheckForIntersect(TTesselator *pTess, TActiveRegion *pRegUp)
{
	TActiveRegion *pRegLo = RegionBelow(pRegUp);
	THalfEdge *pEdgeUp = pRegUp->pEdgeUp;
	THalfEdge *pEdgeLo = pRegLo->pEdgeUp;
	TVertex *pOrgUp = pEdgeUp->pOrigin;
	TVertex *pOrgLo = pEdgeLo->pOrigin;
	TVertex *pDstUp = pEdgeUp->Dst;
	TVertex *pDstLo = pEdgeLo->Dst;
	float tMinUp, tMaxLo;
	TVertex isect, *pOrgMin;
	THalfEdge *pEdge;

	assert(!VertEq(pDstLo, pDstUp));
	assert(EdgeSign (pDstUp, pTess->pVEvent, pOrgUp) <= 0);
	assert(EdgeSign (pDstLo, pTess->pVEvent, pOrgLo) >= 0);
	assert(pOrgUp != pTess->pVEvent && pOrgLo != pTess->pVEvent);
	assert(!pRegUp->bFixUpperEdge && ! pRegLo->bFixUpperEdge);

	if (pOrgUp == pOrgLo) return false;	/* right endpoints are the same */

	tMinUp = MIN(pOrgUp->t, pDstUp->t);
	tMaxLo = MAX(pOrgLo->t, pDstLo->t);
	if (tMinUp > tMaxLo) return false;	/* t ranges do not overlap */

	if (VertLeq(pOrgUp, pOrgLo)) 
    {
		if (EdgeSign(pDstLo, pOrgUp, pOrgLo) > 0) return false;
	}
    else 
    {
		if (EdgeSign(pDstUp, pOrgLo, pOrgUp) < 0)  return false;
	}

	/* At this point the edges intersect, at least marginally */
	DebugEvent(pTess);

	tessEdgeIntersect(pDstUp, pOrgUp, pDstLo, pOrgLo, &isect);
	/* The following properties are guaranteed: */
	assert(MIN(pOrgUp->t, pDstUp->t)  <= isect.t);
	assert(isect.t <= MAX(pOrgLo->t, pDstLo->t));
	assert(MIN (pDstLo->s, pDstUp->s)  <= isect.s);
	assert(isect.s <= MAX(pOrgLo->s, pOrgUp->s));

	if (VertLeq(&isect, pTess->pVEvent)) 
    {
		/* The intersection point lies slightly to the left of the sweep line,
		* so move it until it''s slightly to the right of the sweep line.
		* (If we had perfect numerical precision, this would never happen
		* in the first place).  The easiest and safest thing to do is
		* replace the intersection by tess->event.
		*/
		isect.s = pTess->pVEvent->s;
		isect.t = pTess->pVEvent->t;
	}
	/* Similarly, if the computed intersection lies to the right of the
	* rightmost origin (which should rarely happen), it can cause
	* unbelievable inefficiency on sufficiently degenerate inputs.
	* (If you have the test program, try running test54.d with the
	* "X zoom" option turned on).
	*/
	pOrgMin = VertLeq(pOrgUp, pOrgLo) ? pOrgUp : pOrgLo;
	if (VertLeq(pOrgMin, &isect)) 
    {
		isect.s = pOrgMin->s;
		isect.t = pOrgMin->t;
	}

	if (VertEq(&isect, pOrgUp) || VertEq(&isect, pOrgLo)) 
    {
		/* Easy case -- intersection at one of the right endpoints */
		(void) CheckForRightSplice(pTess, pRegUp);
		return false;
	}

	if  (  (!VertEq(pDstUp, pTess->pVEvent)
		&& EdgeSign(pDstUp, pTess->pVEvent, &isect) >= 0)
		|| (!VertEq(pDstLo, pTess->pVEvent)
		&& EdgeSign(pDstLo, pTess->pVEvent, &isect) <= 0))
	{
		/* Very unusual -- the new upper or lower edge would pass on the
		* wrong side of the sweep event, or through it.  This can happen
		* due to very small numerical errors in the intersection calculation.
		*/
		if (pDstLo == pTess->pVEvent) 
        {
			/* Splice dstLo into eUp, and process the new region(s) */
			if (tessMeshSplitEdge(pTess->pMesh, pEdgeUp->Sym) == NULL) longjmp(pTess->env,1);
			if (!tessMeshSplice(pTess->pMesh, pEdgeLo->Sym, pEdgeUp)) longjmp(pTess->env,1);
			pRegUp = TopLeftRegion(pTess, pRegUp);
			if (pRegUp == NULL) longjmp(pTess->env,1);
			pEdgeUp = RegionBelow(pRegUp)->pEdgeUp;
			FinishLeftRegions(pTess, RegionBelow(pRegUp), pRegLo);
			AddRightEdges(pTess, pRegUp, pEdgeUp->Oprev, pEdgeUp, pEdgeUp, true);
			return true;
		}
		if (pDstUp == pTess->pVEvent) 
        {
			/* Splice dstUp into eLo, and process the new region(s) */
			if (tessMeshSplitEdge(pTess->pMesh, pEdgeLo->Sym) == NULL) longjmp(pTess->env,1);
			if (!tessMeshSplice(pTess->pMesh, pEdgeUp->Lnext, pEdgeLo->Oprev)) longjmp(pTess->env,1); 
			pRegLo = pRegUp;
			pRegUp = TopRightRegion(pRegUp);
			pEdge = RegionBelow(pRegUp)->pEdgeUp->Rprev;
			pRegLo->pEdgeUp = pEdgeLo->Oprev;
			pEdgeLo = FinishLeftRegions(pTess, pRegLo, NULL);
			AddRightEdges(pTess, pRegUp, pEdgeLo->Onext, pEdgeUp->Rprev, pEdge, true);
			return true;
		}
		/* Special case: called from ConnectRightVertex.  If either
		* edge passes on the wrong side of tess->event, split it
		* (and wait for ConnectRightVertex to splice it appropriately).
		*/
		if (EdgeSign(pDstUp, pTess->pVEvent, &isect) >= 0) 
        {
			RegionAbove(pRegUp)->bDirty = pRegUp->bDirty = true;
			if (tessMeshSplitEdge(pTess->pMesh, pEdgeUp->Sym) == NULL) longjmp(pTess->env,1);
			pEdgeUp->pOrigin->s = pTess->pVEvent->s;
			pEdgeUp->pOrigin->t = pTess->pVEvent->t;
		}
		if (EdgeSign(pDstLo, pTess->pVEvent, &isect) <= 0) 
        {
			pRegUp->bDirty = pRegLo->bDirty = true;
			if (tessMeshSplitEdge(pTess->pMesh, pEdgeLo->Sym) == NULL) longjmp(pTess->env,1);
			pEdgeLo->pOrigin->s = pTess->pVEvent->s;
			pEdgeLo->pOrigin->t = pTess->pVEvent->t;
		}
		/* leave the rest for ConnectRightVertex */
		return false;
	}

	/* General case -- split both edges, splice into new vertex.
	* When we do the splice operation, the order of the arguments is
	* arbitrary as far as correctness goes.  However, when the operation
	* creates a new face, the work done is proportional to the size of
	* the new face.  We expect the faces in the processed part of
	* the mesh (ie. eUp->Lface) to be smaller than the faces in the
	* unprocessed original contours (which will be eLo->Oprev->Lface).
	*/
	if (tessMeshSplitEdge(pTess->pMesh, pEdgeUp->Sym) == NULL) longjmp(pTess->env,1);
	if (tessMeshSplitEdge(pTess->pMesh, pEdgeLo->Sym) == NULL) longjmp(pTess->env,1);
	if (!tessMeshSplice(pTess->pMesh, pEdgeLo->Oprev, pEdgeUp)) longjmp(pTess->env,1);
	pEdgeUp->pOrigin->s = isect.s;
	pEdgeUp->pOrigin->t = isect.t;
	pEdgeUp->pOrigin->pqHandle = pqInsert(&pTess->Alloc, pTess->pq, pEdgeUp->pOrigin);
	if (pEdgeUp->pOrigin->pqHandle == INV_HANDLE) 
    {
		pqDeletePriorityQ(&pTess->Alloc, pTess->pq);
		pTess->pq = NULL;
		longjmp(pTess->env,1);
	}
	GetIntersectData(pTess, pEdgeUp->pOrigin, pOrgUp, pDstUp, pOrgLo, pDstLo);
	RegionAbove(pRegUp)->bDirty = pRegUp->bDirty = pRegLo->bDirty = true;
	return false;
}

/*
* When the upper or lower edge of any region changes, the region is
* marked "dirty".  This routine walks through all the dirty regions
* and makes sure that the dictionary invariants are satisfied
* (see the comments at the beginning of this file).  Of course
* new dirty regions can be created as we make changes to restore
* the invariants.
*/
static void WalkDirtyRegions(TTesselator *pTess, TActiveRegion *pRegUp)
{
	TActiveRegion *pRegLo = RegionBelow(pRegUp);
	THalfEdge *pEdgeUp = NULL, *pEdgeLo = NULL;

	for (;;)  
    {
		/* Find the lowest dirty region (we walk from the bottom up). */
		while (pRegLo->bDirty) 
        {
			pRegUp = pRegLo;
			pRegLo = RegionBelow(pRegLo);
		}
		if (!pRegUp->bDirty) 
        {
			pRegLo = pRegUp;
			pRegUp = RegionAbove(pRegUp);
			if (pRegUp == NULL || ! pRegUp->bDirty)
            {
				/* We've walked all the dirty regions */
				return;
			}
		}
		pRegUp->bDirty = false;
		pEdgeUp = pRegUp->pEdgeUp;
		pEdgeLo = pRegLo->pEdgeUp;

		if (pEdgeUp->Dst != pEdgeLo->Dst) 
        {
			/* Check that the edge ordering is obeyed at the Dst vertices. */
			if (CheckForLeftSplice(pTess, pRegUp)) 
            {

				/* If the upper or lower edge was marked fixUpperEdge, then
				* we no longer need it (since these edges are needed only for
				* vertices which otherwise have no right-going edges).
				*/
				if (pRegLo->bFixUpperEdge) 
                {
					DeleteRegion(pTess, pRegLo);
					if (!tessMeshDelete(pTess->pMesh, pEdgeLo)) longjmp(pTess->env,1);
					pRegLo = RegionBelow(pRegUp);
					pEdgeLo = pRegLo->pEdgeUp;
				} 
                else if (pRegUp->bFixUpperEdge) 
                {
					DeleteRegion(pTess, pRegUp);
					if (!tessMeshDelete(pTess->pMesh, pEdgeUp)) longjmp(pTess->env,1);
					pRegUp = RegionAbove(pRegLo);
					pEdgeUp = pRegUp->pEdgeUp;
				}
			}
		}
		if (pEdgeUp->pOrigin != pEdgeLo->pOrigin) 
        {
			if (pEdgeUp->Dst != pEdgeLo->Dst
				&& ! pRegUp->bFixUpperEdge && ! pRegLo->bFixUpperEdge
				&& (pEdgeUp->Dst == pTess->pVEvent || pEdgeLo->Dst == pTess->pVEvent)) 
			{
				/* When all else fails in CheckForIntersect(), it uses tess->event
				* as the intersection location.  To make this possible, it requires
				* that tess->event lie between the upper and lower edges, and also
				* that neither of these is marked fixUpperEdge (since in the worst
				* case it might splice one of these edges into tess->event, and
				* violate the invariant that fixable edges are the only right-going
				* edge from their associated vertex).
				*/
				if (CheckForIntersect(pTess, pRegUp)) 
                {
					/* WalkDirtyRegions() was called recursively; we're done */
					return;
				}
			} 
            else 
            {
				/* Even though we can't use CheckForIntersect(), the Org vertices
				* may violate the dictionary edge ordering.  Check and correct this.
				*/
				(void) CheckForRightSplice(pTess, pRegUp);
			}
		}
		if (pEdgeUp->pOrigin == pEdgeLo->pOrigin && pEdgeUp->Dst == pEdgeLo->Dst) 
        {
			/* A degenerate loop consisting of only two edges -- delete it. */
			AddWinding(pEdgeLo, pEdgeUp);
			DeleteRegion(pTess, pRegUp);
			if (!tessMeshDelete(pTess->pMesh, pEdgeUp)) longjmp(pTess->env,1);
			pRegUp = RegionAbove(pRegLo);
		}
	}
}


/*
* Purpose: connect a "right" vertex vEvent (one where all edges go left)
* to the unprocessed portion of the mesh.  Since there are no right-going
* edges, two regions (one above vEvent and one below) are being merged
* into one.  "regUp" is the upper of these two regions.
*
* There are two reasons for doing this (adding a right-going edge):
*  - if the two regions being merged are "inside", we must add an edge
*    to keep them separated (the combined region would not be monotone).
*  - in any case, we must leave some record of vEvent in the dictionary,
*    so that we can merge vEvent with features that we have not seen yet.
*    For example, maybe there is a vertical edge which passes just to
*    the right of vEvent; we would like to splice vEvent into this edge.
*
* However, we don't want to connect vEvent to just any vertex.  We don''t
* want the new edge to cross any other edges; otherwise we will create
* intersection vertices even when the input data had no self-intersections.
* (This is a bad thing; if the user's input data has no intersections,
* we don't want to generate any false intersections ourselves.)
*
* Our eventual goal is to connect vEvent to the leftmost unprocessed
* vertex of the combined region (the union of regUp and regLo).
* But because of unseen vertices with all right-going edges, and also
* new vertices which may be created by edge intersections, we don''t
* know where that leftmost unprocessed vertex is.  In the meantime, we
* connect vEvent to the closest vertex of either chain, and mark the region
* as "fixUpperEdge".  This flag says to delete and reconnect this edge
* to the next processed vertex on the boundary of the combined region.
* Quite possibly the vertex we connected to will turn out to be the
* closest one, in which case we won''t need to make any changes.
*/
static void ConnectRightVertex (
    TTesselator *pTess, TActiveRegion *pRegUp, THalfEdge *pEdgeBottomLeft)
{
	THalfEdge *pEdgeNew = NULL;
	THalfEdge *pEdgeTopLeft = pEdgeBottomLeft->Onext;
	TActiveRegion *pRegLo = RegionBelow(pRegUp);
	THalfEdge *pEdgeUp = pRegUp->pEdgeUp;
	THalfEdge *pEdgeLo = pRegLo->pEdgeUp;
	int bDegenerate = false;

	if (pEdgeUp->Dst != pEdgeLo->Dst) 
    {
		(void) CheckForIntersect(pTess, pRegUp);
	}

	/* Possible new degeneracies: upper or lower edge of regUp may pass
	* through vEvent, or may coincide with new intersection vertex
	*/
	if (VertEq(pEdgeUp->pOrigin, pTess->pVEvent)) 
    {
		if (!tessMeshSplice(pTess->pMesh, pEdgeTopLeft->Oprev, pEdgeUp)) longjmp(pTess->env,1);
		pRegUp = TopLeftRegion(pTess, pRegUp);
		if (pRegUp == NULL) longjmp(pTess->env,1);
		pEdgeTopLeft = RegionBelow(pRegUp)->pEdgeUp;
		FinishLeftRegions(pTess, RegionBelow(pRegUp), pRegLo);
		bDegenerate = true;
	}
	if (VertEq(pEdgeLo->pOrigin, pTess->pVEvent)) 
    {
		if (!tessMeshSplice(pTess->pMesh, pEdgeBottomLeft, pEdgeLo->Oprev)) longjmp(pTess->env,1);
		pEdgeBottomLeft = FinishLeftRegions(pTess, pRegLo, NULL);
		bDegenerate = true;
	}
	if (bDegenerate) 
    {
		AddRightEdges(pTess, pRegUp, pEdgeBottomLeft->Onext, pEdgeTopLeft, pEdgeTopLeft, true);
		return;
	}

	/* Non-degenerate situation -- need to add a temporary, fixable edge.
	* Connect to the closer of eLo->Org, eUp->Org.
	*/
	if (VertLeq(pEdgeLo->pOrigin, pEdgeUp->pOrigin)) 
    {
		pEdgeNew = pEdgeLo->Oprev;
	} 
    else 
    {
		pEdgeNew = pEdgeUp;
	}
	pEdgeNew = tessMeshConnect(pTess->pMesh, pEdgeBottomLeft->Lprev, pEdgeNew);
	if (pEdgeNew == NULL) longjmp(pTess->env,1);

	/* Prevent cleanup, otherwise eNew might disappear before we've even
	* had a chance to mark it as a temporary edge.
	*/
	AddRightEdges(pTess, pRegUp, pEdgeNew, pEdgeNew->Onext, pEdgeNew->Onext, false);
	pEdgeNew->Sym->pActiveRegion->bFixUpperEdge = true;
	WalkDirtyRegions(pTess, pRegUp);
}

/* Because vertices at exactly the same location are merged together
* before we process the sweep event, some degenerate cases can't occur.
* However if someone eventually makes the modifications required to
* merge features which are close together, the cases below marked
* TOLERANCE_NONZERO will be useful.  They were debugged before the
* code to merge identical vertices in the main loop was added.
*/
#define TOLERANCE_NONZERO	false

/*
* The event vertex lies exacty on an already-processed edge or vertex.
* Adding the new vertex involves splicing it into the already-processed
* part of the mesh.
*/
static void ConnectLeftDegenerate (
    TTesselator *pTess, TActiveRegion *pRegUp, TVertex *pVEvent)
{
	THalfEdge *pEdge, *pEdgeTopLeft, *pEdgeTopRight, *pEdgeLast;
	TActiveRegion *pRegion;

	pEdge = pRegUp->pEdgeUp;
	if (VertEq(pEdge->pOrigin, pVEvent)) 
    {
		/* e->Org is an unprocessed vertex - just combine them, and wait
		* for e->Org to be pulled from the queue
		*/
		assert(TOLERANCE_NONZERO);
		SpliceMergeVertices(pTess, pEdge, pVEvent->pHalfEdge);
		return;
	}

	if (!VertEq (pEdge->Dst, pVEvent)) 
    {
		/* General case -- splice vEvent into edge e which passes through it */
		if (tessMeshSplitEdge(pTess->pMesh, pEdge->Sym) == NULL) longjmp(pTess->env,1);
		if (pRegUp->bFixUpperEdge) 
        {
			/* This edge was fixable -- delete unused portion of original edge */
			if (!tessMeshDelete(pTess->pMesh, pEdge->Onext)) longjmp(pTess->env,1);
			pRegUp->bFixUpperEdge = false;
		}
		if (!tessMeshSplice(pTess->pMesh, pVEvent->pHalfEdge, pEdge)) longjmp(pTess->env,1);
		SweepEvent(pTess, pVEvent);	/* recurse */
		return;
	}

	/* vEvent coincides with e->Dst, which has already been processed.
	* Splice in the additional right-going edges.
	*/
	assert(TOLERANCE_NONZERO);
	pRegUp = TopRightRegion(pRegUp);
	pRegion = RegionBelow(pRegUp);
	pEdgeTopRight = pRegion->pEdgeUp->Sym;
	pEdgeTopLeft = pEdgeLast = pEdgeTopRight->Onext;
	if (pRegion->bFixUpperEdge) 
    {
		/* Here e->Dst has only a single fixable edge going right.
		* We can delete it since now we have some real right-going edges.
		*/
		assert(pEdgeTopLeft != pEdgeTopRight);   /* there are some left edges too */
		DeleteRegion(pTess, pRegion);
		if (!tessMeshDelete(pTess->pMesh, pEdgeTopRight)) longjmp(pTess->env,1);
		pEdgeTopRight = pEdgeTopLeft->Oprev;
	}
	if (!tessMeshSplice(pTess->pMesh, pVEvent->pHalfEdge, pEdgeTopRight)) longjmp(pTess->env,1);
	if (!EdgeGoesLeft(pEdgeTopLeft)) 
    {
		/* e->Dst had no left-going edges -- indicate this to AddRightEdges() */
		pEdgeTopLeft = NULL;
	}
	AddRightEdges(pTess, pRegUp, pEdgeTopRight->Onext, pEdgeLast, pEdgeTopLeft, true);
}


/*
* Purpose: connect a "left" vertex (one where both edges go right)
* to the processed portion of the mesh.  Let R be the active region
* containing vEvent, and let U and L be the upper and lower edge
* chains of R.  There are two possibilities:
*
* - the normal case: split R into two regions, by connecting vEvent to
*   the rightmost vertex of U or L lying to the left of the sweep line
*
* - the degenerate case: if vEvent is close enough to U or L, we
*   merge vEvent into that edge chain.  The subcases are:
*	- merging with the rightmost vertex of U or L
*	- merging with the active edge of U or L
*	- merging with an already-processed portion of U or L
*/
static void ConnectLeftVertex(TTesselator *pTess, TVertex *pVEvent)
{
	TActiveRegion *pRegUp = NULL, *pRegLo = NULL, *pReg = NULL;
	THalfEdge *pEdgeUp = NULL, *pEdgeLo = NULL, *pEdgeNew = NULL;
	TActiveRegion tmp;

	/* assert (vEvent->anEdge->Onext->Onext == vEvent->anEdge) ; */
	/* Get a pointer to the active region containing vEvent */
	tmp.pEdgeUp = pVEvent->pHalfEdge->Sym;
	/* __GL_DICTLISTKEY */ /* tessDictListSearch */
	pRegUp = (TActiveRegion *)dictKey(dictSearch(pTess->pDict, &tmp));
	pRegLo = RegionBelow(pRegUp);
	if (!pRegLo) 
    {
		// This may happen if the input polygon is coplanar.
		return;
	}
	pEdgeUp = pRegUp->pEdgeUp;
	pEdgeLo = pRegLo->pEdgeUp;

	/* Try merging with U or L first */
	if (EdgeSign(pEdgeUp->Dst, pVEvent, pEdgeUp->pOrigin) == 0) 
    {
		ConnectLeftDegenerate(pTess, pRegUp, pVEvent);
		return;
	}

	/* Connect vEvent to rightmost processed vertex of either chain.
	* e->Dst is the vertex that we will connect to vEvent.
	*/
	pReg = VertLeq(pEdgeLo->Dst, pEdgeUp->Dst) ? pRegUp : pRegLo;

	if (pRegUp->bInside || pReg->bFixUpperEdge) 
    {
		if (pReg == pRegUp) 
        {
			pEdgeNew = tessMeshConnect(pTess->pMesh, pVEvent->pHalfEdge->Sym, pEdgeUp->Lnext);
			if (pEdgeNew == NULL) longjmp(pTess->env,1);
		} 
        else 
        {
			THalfEdge *tempHalfEdge= tessMeshConnect(pTess->pMesh, pEdgeLo->Dnext, pVEvent->pHalfEdge);
			if (tempHalfEdge == NULL) longjmp(pTess->env,1);

			pEdgeNew = tempHalfEdge->Sym;
		}
		if (pReg->bFixUpperEdge) 
        {
			if (!FixUpperEdge(pTess, pReg, pEdgeNew)) longjmp(pTess->env,1);
		} 
        else 
        {
			ComputeWinding(pTess, AddRegionBelow(pTess, pRegUp, pEdgeNew));
		}
		SweepEvent(pTess, pVEvent);
	} 
    else 
    {
		/* The new vertex is in a region which does not belong to the polygon.
		* We don''t need to connect this vertex to the rest of the mesh.
		*/
		AddRightEdges(pTess, pRegUp, pVEvent->pHalfEdge, pVEvent->pHalfEdge, NULL, true);
	}
}


/*
* Does everything necessary when the sweep line crosses a vertex.
* Updates the mesh and the edge dictionary.
*/
static void SweepEvent(TTesselator *pTess, TVertex *pVEvent)
{
	TActiveRegion *pRegUp = NULL, *pRegBelow = NULL;
	THalfEdge *pEdge = NULL, *pEdgeTopLeft = NULL, *pEdgeBottomLeft = NULL;

	pTess->pVEvent = pVEvent;		/* for access in EdgeLeq() */
	DebugEvent(pTess);

	/* Check if this vertex is the right endpoint of an edge that is
	* already in the dictionary.  In this case we don't need to waste
	* time searching for the location to insert new edges.
	*/
	pEdge = pVEvent->pHalfEdge;
	while (pEdge->pActiveRegion == NULL) 
    {
		pEdge = pEdge->Onext;
		if (pEdge == pVEvent->pHalfEdge)
       	{
            /* All edges go right -- not incident to any processed edges */
            ConnectLeftVertex(pTess, pVEvent);
			return;
        }
    }

	/* Processing consists of two phases: first we "finish" all the
	* active regions where both the upper and lower edges terminate
	* at vEvent (ie. vEvent is closing off these regions).
	* We mark these faces "inside" or "outside" the polygon according
	* to their winding number, and delete the edges from the dictionary.
	* This takes care of all the left-going edges from vEvent.
	*/
	pRegUp = TopLeftRegion(pTess, pEdge->pActiveRegion);
	if (pRegUp == NULL) longjmp(pTess->env,1);
	pRegBelow = RegionBelow(pRegUp);
	pEdgeTopLeft = pRegBelow->pEdgeUp;
	pEdgeBottomLeft = FinishLeftRegions(pTess, pRegBelow, NULL);

	/* Next we process all the right-going edges from vEvent.  This
	* involves adding the edges to the dictionary, and creating the
	* associated "active regions" which record information about the
	* regions between adjacent dictionary edges.
	*/
	if (pEdgeBottomLeft->Onext == pEdgeTopLeft) 
	{
		/* No right-going edges -- add a temporary "fixable" edge */
		ConnectRightVertex(pTess, pRegUp, pEdgeBottomLeft);
	} 
    else 
    {
		AddRightEdges(pTess, pRegUp, pEdgeBottomLeft->Onext, pEdgeTopLeft, pEdgeTopLeft, true);
	}
}


/* Make the sentinel coordinates big enough that they will never be
* merged with real input features.
*/
/*
* We add two sentinel edges above and below all other edges,
* to avoid special cases at the top and bottom.
*/
static void AddSentinel(TTesselator *pTess, float smin, float smax, float t)
{
	THalfEdge *e;
	TActiveRegion *reg = (TActiveRegion *)BucketAlloc(pTess->pRegionPool);
	if (reg == NULL) longjmp(pTess->env,1);

	e = tessMeshMakeEdge(pTess->pMesh);
	if (e == NULL) longjmp(pTess->env,1);

	e->pOrigin->s = smax;
	e->pOrigin->t = t;
	e->Dst->s = smin;
	e->Dst->t = t;
	pTess->pVEvent = e->Dst;		/* initialize it */

	reg->pEdgeUp = e;
	reg->nWindingNumber = 0;
	reg->bInside = false;
	reg->bFixUpperEdge = false;
	reg->bSentinel = true;
	reg->bDirty = false;
	reg->pNodeUp = dictInsert(pTess->pDict, reg);
	if (reg->pNodeUp == NULL) longjmp(pTess->env,1);
}


/*
* We maintain an ordering of edge intersections with the sweep line.
* This order is maintained in a dynamic dictionary.
*/
static void InitEdgeDict(TTesselator *pTess)
{
	float w, h;
	float smin, smax, tmin, tmax;

	pTess->pDict = dictNewDict(&pTess->Alloc, pTess, (int (*)(void *, TDictKey, TDictKey)) EdgeLeq) ;
	if (pTess->pDict == NULL) longjmp(pTess->env,1);

	w = (pTess->fBMax[0] - pTess->fBMin[0]);
	h = (pTess->fBMax[1] - pTess->fBMin[1]);

	smin = pTess->fBMin[0] - w;
	smax = pTess->fBMax[0] + w;
	tmin = pTess->fBMin[1] - h;
	tmax = pTess->fBMax[1] + h;

	AddSentinel (pTess, smin, smax, tmin) ;
	AddSentinel (pTess, smin, smax, tmax) ;
}


static void DoneEdgeDict(TTesselator *pTess)
{
	TActiveRegion *pRegion;
	int nFixedEdges = 0;

	while ((pRegion = (TActiveRegion *)dictKey (dictMin (pTess->pDict) )) != NULL) 
    {
		/*
		* At the end of all processing, the dictionary should contain
		* only the two sentinel edges, plus at most one "fixable" edge
		* created by ConnectRightVertex().
		*/
		if (!pRegion->bSentinel) 
        {
			assert(pRegion->bFixUpperEdge);
			assert(++nFixedEdges == 1);
		}
		assert(pRegion->nWindingNumber == 0);
		DeleteRegion(pTess, pRegion);
		/*    tessMeshDelete (reg->eUp) ;*/
	}
	dictDeleteDict(&pTess->Alloc, pTess->pDict);
}


/*
* Remove zero-length edges, and contours with fewer than 3 vertices.
*/
static void RemoveDegenerateEdges(TTesselator *pTess)
{
	THalfEdge *pEdge, *pEdgeNext, *eLnext;
	THalfEdge *pEdgeHead = &pTess->pMesh->eHead;

	/*LINTED*/
	for (pEdge = pEdgeHead->pNext; pEdge != pEdgeHead; pEdge = pEdgeNext) 
    {
		pEdgeNext = pEdge->pNext;
		eLnext = pEdge->Lnext;

		if (VertEq(pEdge->pOrigin, pEdge->Dst) && pEdge->Lnext->Lnext != pEdge) 
        {
			/* Zero-length edge, contour has at least 3 edges */

			SpliceMergeVertices(pTess, eLnext, pEdge);	/* deletes e->Org */
			if (!tessMeshDelete(pTess->pMesh, pEdge)) longjmp(pTess->env,1); /* e is a self-loop */
			pEdge = eLnext;
			eLnext = pEdge->Lnext;
		}
		if (eLnext->Lnext == pEdge) 
        {
			/* Degenerate contour (one or two edges) */

			if (eLnext != pEdge) 
            {
				if (eLnext == pEdgeNext || eLnext == pEdgeNext->Sym) { pEdgeNext = pEdgeNext->pNext; }
				if (!tessMeshDelete(pTess->pMesh, eLnext)) longjmp(pTess->env,1);
			}
			if (pEdge == pEdgeNext || pEdge == pEdgeNext->Sym) { pEdgeNext = pEdgeNext->pNext; }
			if (!tessMeshDelete(pTess->pMesh, pEdge)) longjmp(pTess->env, 1);
		}
	}
}

/*
* Insert all vertices into the priority queue which determines the
* order in which vertices cross the sweep line.
*/
static int InitPriorityQ(TTesselator *pTess)
{
	TPriorityQ *pq = NULL;
	TVertex *pVertex = NULL, *pVertexHead = NULL;
	int nVertexCount = 0;
	
	pVertexHead = &pTess->pMesh->vHead;
	for (pVertex = pVertexHead->pNext; pVertex != pVertexHead; pVertex = pVertex->pNext) 
    {
		nVertexCount++;
	}
	/* Make sure there is enough space for sentinels. */
	nVertexCount += MAX(8, pTess->Alloc.nExtraVertices);
	
	pq = pTess->pq = pqNewPriorityQ(&pTess->Alloc, nVertexCount, (int (*)(PQkey, PQkey))tessVertLeq);
	if (pq == NULL) return 0;

	pVertexHead = &pTess->pMesh->vHead;
	for (pVertex = pVertexHead->pNext; pVertex != pVertexHead; pVertex = pVertex->pNext)
    {
		pVertex->pqHandle = pqInsert(&pTess->Alloc, pq, pVertex);
		if (pVertex->pqHandle == INV_HANDLE)
			break;
	}
	if (pVertex != pVertexHead || !pqInit(&pTess->Alloc, pq)) 
    {
		pqDeletePriorityQ(&pTess->Alloc, pTess->pq);
		pTess->pq = NULL;
		return 0;
	}

	return 1;
}


static void DonePriorityQ(TTesselator *pTess)
{
	pqDeletePriorityQ(&pTess->Alloc, pTess->pq);
}

/*
* Delete any degenerate faces with only two edges.  WalkDirtyRegions()
* will catch almost all of these, but it won't catch degenerate faces
* produced by splice operations on already-processed edges.
* The two places this can happen are in FinishLeftRegions(), when
* we splice in a "temporary" edge produced by ConnectRightVertex(),
* and in CheckForLeftSplice(), where we splice already-processed
* edges to ensure that our dictionary invariants are not violated
* by numerical errors.
*
* In both these cases it is *very* dangerous to delete the offending
* edge at the time, since one of the routines further up the stack
* will sometimes be keeping a pointer to that edge.
*/
static int RemoveDegenerateFaces(TTesselator *pTess, TMesh *pMesh)
{
	TFace *pFace = NULL, *pFaceNext = NULL;
	THalfEdge *fEdge = NULL;

	/*LINTED*/
	for (pFace = pMesh->fHead.pNext; pFace != &pMesh->fHead; pFace = pFaceNext) 
    {
		pFaceNext = pFace->pNext;
		fEdge = pFace->pHalfEdge;
		assert(fEdge->Lnext != fEdge);

		if (fEdge->Lnext->Lnext == fEdge) 
        {
			/* A face with only two edges */
			AddWinding(fEdge->Onext, fEdge);
			if (!tessMeshDelete(pTess->pMesh, fEdge)) return 0;
		}
	}
	return 1;
}

/*
* tessComputeInterior (tess)  computes the planar arrangement specified
* by the given contours, and further subdivides this arrangement
* into regions.  Each region is marked "inside" if it belongs
* to the polygon, according to the rule given by tess->windingRule.
* Each interior region is guaranteed be monotone.
*/
int tessComputeInterior(TTesselator *pTess)
{
	TVertex *pVertex = NULL, *pVertexNext = NULL;

	/* Each vertex defines an event for our sweep line.  Start by inserting
	* all the vertices in a priority queue.  Events are processed in
	* lexicographic order, ie.
	*
	*	e1 < e2  iff  e1.x < e2.x || (e1.x == e2.x && e1.y < e2.y)
	*/
	RemoveDegenerateEdges(pTess);
	if (!InitPriorityQ(pTess)) return 0; /* if error */
	InitEdgeDict(pTess);

	while ((pVertex = (TVertex *)pqExtractMin(pTess->pq)) != NULL) 
    {
		for (;;)
        {
			pVertexNext = (TVertex *)pqMinimum(pTess->pq);
			if (pVertexNext == NULL || !VertEq(pVertexNext, pVertex)) break;

			/* Merge together all vertices at exactly the same location.
			* This is more efficient than processing them one at a time,
			* simplifies the code (see ConnectLeftDegenerate), and is also
			* important for correct handling of certain degenerate cases.
			* For example, suppose there are two identical edges A and B
			* that belong to different contours (so without this code they would
			* be processed by separate sweep events).  Suppose another edge C
			* crosses A and B from above.  When A is processed, we split it
			* at its intersection point with C.  However this also splits C,
			* so when we insert B we may compute a slightly different
			* intersection point.  This might leave two edges with a small
			* gap between them.  This kind of error is especially obvious
			* when using boundary extraction (TESS_BOUNDARY_ONLY).
			*/
			pVertexNext = (TVertex *)pqExtractMin(pTess->pq);
			SpliceMergeVertices(pTess, pVertex->pHalfEdge, pVertexNext->pHalfEdge);
		}
		SweepEvent(pTess, pVertex);
	}

	/* Set tess->event for debugging purposes */
	pTess->pVEvent = ((TActiveRegion *)dictKey(dictMin(pTess->pDict)))->pEdgeUp->pOrigin;
	DebugEvent(pTess);
	DoneEdgeDict(pTess);
	DonePriorityQ(pTess);

	if (!RemoveDegenerateFaces(pTess, pTess->pMesh)) return 0;
	tessMeshCheckMesh(pTess->pMesh);

	return 1;
}
