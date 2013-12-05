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

//#include "tesos.h"
#include <stddef.h>
#include <assert.h>
#include "mesh.h"
#include "geom.h"
#include "bucketalloc.h"

#define TRUE 1
#define FALSE 0

/************************ Utility Routines ************************/

/* Allocate and free half-edges in pairs for efficiency.
* The *only* place that should use this fact is allocation/free.
*/
typedef struct { THalfEdge e, eSym; } EdgePair;

/* MakeEdge creates a new pair of half-edges which form their own loop.
* No vertex or face structures are allocated, but these must be assigned
* before the current edge operation is completed.
*/
static THalfEdge *MakeEdge( TMesh* mesh, THalfEdge *eNext )
{
	THalfEdge *e;
	THalfEdge *eSym;
	THalfEdge *ePrev;
	EdgePair *pair = (EdgePair *)bucketAlloc( mesh->pEdgeBucket );
	if (pair == NULL) return NULL;

	e = &pair->e;
	eSym = &pair->eSym;

	/* Make sure eNext points to the first edge of the edge pair */
	if( eNext->Sym < eNext ) { eNext = eNext->Sym; }

	/* Insert in circular doubly-linked list before eNext.
	* Note that the prev pointer is stored in Sym->next.
	*/
	ePrev = eNext->Sym->pNext;
	eSym->pNext = ePrev;
	ePrev->Sym->pNext = e;
	e->pNext = eNext;
	eNext->Sym->pNext = eSym;

	e->Sym = eSym;
	e->Onext = e;
	e->Lnext = eSym;
	e->pOrigin = NULL;
	e->Lface = NULL;
	e->nWinding = 0;
	e->pActiveRegion = NULL;

	eSym->Sym = e;
	eSym->Onext = eSym;
	eSym->Lnext = e;
	eSym->pOrigin = NULL;
	eSym->Lface = NULL;
	eSym->nWinding = 0;
	eSym->pActiveRegion = NULL;

	return e;
}

/* Splice( a, b ) is best described by the Guibas/Stolfi paper or the
* CS348a notes (see mesh.h).  Basically it modifies the mesh so that
* a->Onext and b->Onext are exchanged.  This can have various effects
* depending on whether a and b belong to different face or vertex rings.
* For more explanation see tessMeshSplice() below.
*/
static void Splice( THalfEdge *a, THalfEdge *b )
{
	THalfEdge *aOnext = a->Onext;
	THalfEdge *bOnext = b->Onext;

	aOnext->Sym->Lnext = b;
	bOnext->Sym->Lnext = a;
	a->Onext = bOnext;
	b->Onext = aOnext;
}

/* MakeVertex( newVertex, eOrig, vNext ) attaches a new vertex and makes it the
* origin of all edges in the vertex loop to which eOrig belongs. "vNext" gives
* a place to insert the new vertex in the global vertex list.  We insert
* the new vertex *before* vNext so that algorithms which walk the vertex
* list will not see the newly created vertices.
*/
static void MakeVertex( TVertex *newVertex, 
					   THalfEdge *eOrig, TVertex *vNext )
{
	THalfEdge *e;
	TVertex *vPrev;
	TVertex *vNew = newVertex;

	assert(vNew != NULL);

	/* insert in circular doubly-linked list before vNext */
	vPrev = vNext->pPrev;
	vNew->pPrev = vPrev;
	vPrev->pNext = vNew;
	vNew->pNext = vNext;
	vNext->pPrev = vNew;

	vNew->pHalfEdge = eOrig;
	/* leave coords, s, t undefined */

	/* fix other edges on this vertex loop */
	e = eOrig;
	do {
		e->pOrigin = vNew;
		e = e->Onext;
	} while( e != eOrig );
}

/* MakeFace( newFace, eOrig, fNext ) attaches a new face and makes it the left
* face of all edges in the face loop to which eOrig belongs.  "fNext" gives
* a place to insert the new face in the global face list.  We insert
* the new face *before* fNext so that algorithms which walk the face
* list will not see the newly created faces.
*/
static void MakeFace( TFace *newFace, THalfEdge *eOrig, TFace *fNext )
{
	THalfEdge *e;
	TFace *fPrev;
	TFace *fNew = newFace;

	assert(fNew != NULL); 

	/* insert in circular doubly-linked list before fNext */
	fPrev = fNext->pPrev;
	fNew->pPrev = fPrev;
	fPrev->pNext = fNew;
	fNew->pNext = fNext;
	fNext->pPrev = fNew;

	fNew->pHalfEdge = eOrig;
	fNew->pTrail = NULL;
	fNew->bMarked = FALSE;

	/* The new face is marked "inside" if the old one was.  This is a
	* convenience for the common case where a face has been split in two.
	*/
	fNew->bInside = fNext->bInside;

	/* fix other edges on this face loop */
	e = eOrig;
	do {
		e->Lface = fNew;
		e = e->Lnext;
	} while( e != eOrig );
}

/* KillEdge( eDel ) destroys an edge (the half-edges eDel and eDel->Sym),
* and removes from the global edge list.
*/
static void KillEdge( TMesh *mesh, THalfEdge *eDel )
{
	THalfEdge *ePrev, *eNext;

	/* Half-edges are allocated in pairs, see EdgePair above */
	if( eDel->Sym < eDel ) { eDel = eDel->Sym; }

	/* delete from circular doubly-linked list */
	eNext = eDel->pNext;
	ePrev = eDel->Sym->pNext;
	eNext->Sym->pNext = ePrev;
	ePrev->Sym->pNext = eNext;

	bucketFree( mesh->pEdgeBucket, eDel );
}


/* KillVertex( vDel ) destroys a vertex and removes it from the global
* vertex list.  It updates the vertex loop to point to a given new vertex.
*/
static void KillVertex( TMesh *mesh, TVertex *vDel, TVertex *newOrg )
{
	THalfEdge *e, *eStart = vDel->pHalfEdge;
	TVertex *vPrev, *vNext;

	/* change the origin of all affected edges */
	e = eStart;
	do {
		e->pOrigin = newOrg;
		e = e->Onext;
	} while( e != eStart );

	/* delete from circular doubly-linked list */
	vPrev = vDel->pPrev;
	vNext = vDel->pNext;
	vNext->pPrev = vPrev;
	vPrev->pNext = vNext;

	bucketFree( mesh->pVertexBucket, vDel );
}

/* KillFace( fDel ) destroys a face and removes it from the global face
* list.  It updates the face loop to point to a given new face.
*/
static void KillFace( TMesh *mesh, TFace *fDel, TFace *newLface )
{
	THalfEdge *e, *eStart = fDel->pHalfEdge;
	TFace *fPrev, *fNext;

	/* change the left face of all affected edges */
	e = eStart;
	do {
		e->Lface = newLface;
		e = e->Lnext;
	} while( e != eStart );

	/* delete from circular doubly-linked list */
	fPrev = fDel->pPrev;
	fNext = fDel->pNext;
	fNext->pPrev = fPrev;
	fPrev->pNext = fNext;

	bucketFree( mesh->pFaceBucket, fDel );
}


/****************** Basic Edge Operations **********************/

/* tessMeshMakeEdge creates one edge, two vertices, and a loop (face).
* The loop consists of the two new half-edges.
*/
THalfEdge *tessMeshMakeEdge( TMesh *mesh )
{
	TVertex *newVertex1 = (TVertex*)bucketAlloc(mesh->pVertexBucket);
	TVertex *newVertex2 = (TVertex*)bucketAlloc(mesh->pVertexBucket);
	TFace *newFace = (TFace*)bucketAlloc(mesh->pFaceBucket);
	THalfEdge *e;

	/* if any one is null then all get freed */
	if (newVertex1 == NULL || newVertex2 == NULL || newFace == NULL) {
		if (newVertex1 != NULL) bucketFree( mesh->pVertexBucket, newVertex1 );
		if (newVertex2 != NULL) bucketFree( mesh->pVertexBucket, newVertex2 );
		if (newFace != NULL) bucketFree( mesh->pFaceBucket, newFace );     
		return NULL;
	} 

	e = MakeEdge( mesh, &mesh->eHead );
	if (e == NULL) return NULL;

	MakeVertex( newVertex1, e, &mesh->vHead );
	MakeVertex( newVertex2, e->Sym, &mesh->vHead );
	MakeFace( newFace, e, &mesh->fHead );
	return e;
}


/* tessMeshSplice( eOrg, eDst ) is the basic operation for changing the
* mesh connectivity and topology.  It changes the mesh so that
*	eOrg->Onext <- OLD( eDst->Onext )
*	eDst->Onext <- OLD( eOrg->Onext )
* where OLD(...) means the value before the meshSplice operation.
*
* This can have two effects on the vertex structure:
*  - if eOrg->Org != eDst->Org, the two vertices are merged together
*  - if eOrg->Org == eDst->Org, the origin is split into two vertices
* In both cases, eDst->Org is changed and eOrg->Org is untouched.
*
* Similarly (and independently) for the face structure,
*  - if eOrg->Lface == eDst->Lface, one loop is split into two
*  - if eOrg->Lface != eDst->Lface, two distinct loops are joined into one
* In both cases, eDst->Lface is changed and eOrg->Lface is unaffected.
*
* Some special cases:
* If eDst == eOrg, the operation has no effect.
* If eDst == eOrg->Lnext, the new face will have a single edge.
* If eDst == eOrg->Lprev, the old face will have a single edge.
* If eDst == eOrg->Onext, the new vertex will have a single edge.
* If eDst == eOrg->Oprev, the old vertex will have a single edge.
*/
int tessMeshSplice( TMesh* mesh, THalfEdge *eOrg, THalfEdge *eDst )
{
	int joiningLoops = FALSE;
	int joiningVertices = FALSE;

	if( eOrg == eDst ) return 1;

	if( eDst->pOrigin != eOrg->pOrigin ) {
		/* We are merging two disjoint vertices -- destroy eDst->Org */
		joiningVertices = TRUE;
		KillVertex( mesh, eDst->pOrigin, eOrg->pOrigin );
	}
	if( eDst->Lface != eOrg->Lface ) {
		/* We are connecting two disjoint loops -- destroy eDst->Lface */
		joiningLoops = TRUE;
		KillFace( mesh, eDst->Lface, eOrg->Lface );
	}

	/* Change the edge structure */
	Splice( eDst, eOrg );

	if( ! joiningVertices ) {
		TVertex *newVertex = (TVertex*)bucketAlloc( mesh->pVertexBucket );
		if (newVertex == NULL) return 0;

		/* We split one vertex into two -- the new vertex is eDst->Org.
		* Make sure the old vertex points to a valid half-edge.
		*/
		MakeVertex( newVertex, eDst, eOrg->pOrigin );
		eOrg->pOrigin->pHalfEdge = eOrg;
	}
	if( ! joiningLoops ) {
		TFace *newFace = (TFace*)bucketAlloc( mesh->pFaceBucket );  
		if (newFace == NULL) return 0;

		/* We split one loop into two -- the new loop is eDst->Lface.
		* Make sure the old face points to a valid half-edge.
		*/
		MakeFace( newFace, eDst, eOrg->Lface );
		eOrg->Lface->pHalfEdge = eOrg;
	}

	return 1;
}


/* tessMeshDelete( eDel ) removes the edge eDel.  There are several cases:
* if (eDel->Lface != eDel->Rface), we join two loops into one; the loop
* eDel->Lface is deleted.  Otherwise, we are splitting one loop into two;
* the newly created loop will contain eDel->Dst.  If the deletion of eDel
* would create isolated vertices, those are deleted as well.
*
* This function could be implemented as two calls to tessMeshSplice
* plus a few calls to memFree, but this would allocate and delete
* unnecessary vertices and faces.
*/
int tessMeshDelete( TMesh *mesh, THalfEdge *eDel )
{
	THalfEdge *eDelSym = eDel->Sym;
	int joiningLoops = FALSE;

	/* First step: disconnect the origin vertex eDel->Org.  We make all
	* changes to get a consistent mesh in this "intermediate" state.
	*/
	if( eDel->Lface != eDel->Rface ) {
		/* We are joining two loops into one -- remove the left face */
		joiningLoops = TRUE;
		KillFace( mesh, eDel->Lface, eDel->Rface );
	}

	if( eDel->Onext == eDel ) {
		KillVertex( mesh, eDel->pOrigin, NULL );
	} else {
		/* Make sure that eDel->Org and eDel->Rface point to valid half-edges */
		eDel->Rface->pHalfEdge = eDel->Oprev;
		eDel->pOrigin->pHalfEdge = eDel->Onext;

		Splice( eDel, eDel->Oprev );
		if( ! joiningLoops ) {
			TFace *newFace= (TFace*)bucketAlloc( mesh->pFaceBucket );
			if (newFace == NULL) return 0; 

			/* We are splitting one loop into two -- create a new loop for eDel. */
			MakeFace( newFace, eDel, eDel->Lface );
		}
	}

	/* Claim: the mesh is now in a consistent state, except that eDel->Org
	* may have been deleted.  Now we disconnect eDel->Dst.
	*/
	if( eDelSym->Onext == eDelSym ) {
		KillVertex( mesh, eDelSym->pOrigin, NULL );
		KillFace( mesh, eDelSym->Lface, NULL );
	} else {
		/* Make sure that eDel->Dst and eDel->Lface point to valid half-edges */
		eDel->Lface->pHalfEdge = eDelSym->Oprev;
		eDelSym->pOrigin->pHalfEdge = eDelSym->Onext;
		Splice( eDelSym, eDelSym->Oprev );
	}

	/* Any isolated vertices or faces have already been freed. */
	KillEdge( mesh, eDel );

	return 1;
}


/******************** Other Edge Operations **********************/

/* All these routines can be implemented with the basic edge
* operations above.  They are provided for convenience and efficiency.
*/


/* tessMeshAddEdgeVertex( eOrg ) creates a new edge eNew such that
* eNew == eOrg->Lnext, and eNew->Dst is a newly created vertex.
* eOrg and eNew will have the same left face.
*/
THalfEdge *tessMeshAddEdgeVertex( TMesh *mesh, THalfEdge *eOrg )
{
	THalfEdge *eNewSym;
	THalfEdge *eNew = MakeEdge( mesh, eOrg );
	if (eNew == NULL) return NULL;

	eNewSym = eNew->Sym;

	/* Connect the new edge appropriately */
	Splice( eNew, eOrg->Lnext );

	/* Set the vertex and face information */
	eNew->pOrigin = eOrg->Dst;
	{
		TVertex *newVertex= (TVertex*)bucketAlloc( mesh->pVertexBucket );
		if (newVertex == NULL) return NULL;

		MakeVertex( newVertex, eNewSym, eNew->pOrigin );
	}
	eNew->Lface = eNewSym->Lface = eOrg->Lface;

	return eNew;
}


/* tessMeshSplitEdge( eOrg ) splits eOrg into two edges eOrg and eNew,
* such that eNew == eOrg->Lnext.  The new vertex is eOrg->Dst == eNew->Org.
* eOrg and eNew will have the same left face.
*/
THalfEdge *tessMeshSplitEdge( TMesh *mesh, THalfEdge *eOrg )
{
	THalfEdge *eNew;
	THalfEdge *tempHalfEdge= tessMeshAddEdgeVertex( mesh, eOrg );
	if (tempHalfEdge == NULL) return NULL;

	eNew = tempHalfEdge->Sym;

	/* Disconnect eOrg from eOrg->Dst and connect it to eNew->Org */
	Splice( eOrg->Sym, eOrg->Sym->Oprev );
	Splice( eOrg->Sym, eNew );

	/* Set the vertex and face information */
	eOrg->Dst = eNew->pOrigin;
	eNew->Dst->pHalfEdge = eNew->Sym;	/* may have pointed to eOrg->Sym */
	eNew->Rface = eOrg->Rface;
	eNew->nWinding = eOrg->nWinding;	/* copy old winding information */
	eNew->Sym->nWinding = eOrg->Sym->nWinding;

	return eNew;
}


/* tessMeshConnect( eOrg, eDst ) creates a new edge from eOrg->Dst
* to eDst->Org, and returns the corresponding half-edge eNew.
* If eOrg->Lface == eDst->Lface, this splits one loop into two,
* and the newly created loop is eNew->Lface.  Otherwise, two disjoint
* loops are merged into one, and the loop eDst->Lface is destroyed.
*
* If (eOrg == eDst), the new face will have only two edges.
* If (eOrg->Lnext == eDst), the old face is reduced to a single edge.
* If (eOrg->Lnext->Lnext == eDst), the old face is reduced to two edges.
*/
THalfEdge *tessMeshConnect( TMesh *mesh, THalfEdge *eOrg, THalfEdge *eDst )
{
	THalfEdge *eNewSym;
	int joiningLoops = FALSE;  
	THalfEdge *eNew = MakeEdge( mesh, eOrg );
	if (eNew == NULL) return NULL;

	eNewSym = eNew->Sym;

	if( eDst->Lface != eOrg->Lface ) {
		/* We are connecting two disjoint loops -- destroy eDst->Lface */
		joiningLoops = TRUE;
		KillFace( mesh, eDst->Lface, eOrg->Lface );
	}

	/* Connect the new edge appropriately */
	Splice( eNew, eOrg->Lnext );
	Splice( eNewSym, eDst );

	/* Set the vertex and face information */
	eNew->pOrigin = eOrg->Dst;
	eNewSym->pOrigin = eDst->pOrigin;
	eNew->Lface = eNewSym->Lface = eOrg->Lface;

	/* Make sure the old face points to a valid half-edge */
	eOrg->Lface->pHalfEdge = eNewSym;

	if( ! joiningLoops ) {
		TFace *newFace= (TFace*)bucketAlloc( mesh->pFaceBucket );
		if (newFace == NULL) return NULL;

		/* We split one loop into two -- the new loop is eNew->Lface */
		MakeFace( newFace, eNew, eOrg->Lface );
	}
	return eNew;
}


/******************** Other Operations **********************/

/* tessMeshZapFace( fZap ) destroys a face and removes it from the
* global face list.  All edges of fZap will have a NULL pointer as their
* left face.  Any edges which also have a NULL pointer as their right face
* are deleted entirely (along with any isolated vertices this produces).
* An entire mesh can be deleted by zapping its faces, one at a time,
* in any order.  Zapped faces cannot be used in further mesh operations!
*/
void tessMeshZapFace( TMesh *mesh, TFace *fZap )
{
	THalfEdge *eStart = fZap->pHalfEdge;
	THalfEdge *e, *eNext, *eSym;
	TFace *fPrev, *fNext;

	/* walk around face, deleting edges whose right face is also NULL */
	eNext = eStart->Lnext;
	do {
		e = eNext;
		eNext = e->Lnext;

		e->Lface = NULL;
		if( e->Rface == NULL ) {
			/* delete the edge -- see TESSmeshDelete above */

			if( e->Onext == e ) {
				KillVertex( mesh, e->pOrigin, NULL );
			} else {
				/* Make sure that e->Org points to a valid half-edge */
				e->pOrigin->pHalfEdge = e->Onext;
				Splice( e, e->Oprev );
			}
			eSym = e->Sym;
			if( eSym->Onext == eSym ) {
				KillVertex( mesh, eSym->pOrigin, NULL );
			} else {
				/* Make sure that eSym->Org points to a valid half-edge */
				eSym->pOrigin->pHalfEdge = eSym->Onext;
				Splice( eSym, eSym->Oprev );
			}
			KillEdge( mesh, e );
		}
	} while( e != eStart );

	/* delete from circular doubly-linked list */
	fPrev = fZap->pPrev;
	fNext = fZap->pNext;
	fNext->pPrev = fPrev;
	fPrev->pNext = fNext;

	bucketFree( mesh->pFaceBucket, fZap );
}


/* tessMeshNewMesh() creates a new mesh with no edges, no vertices,
* and no loops (what we usually call a "face").
*/
TMesh *tessMeshNewMesh( TAlloc* alloc )
{
	TVertex *v;
	TFace *f;
	THalfEdge *e;
	THalfEdge *eSym;
	TMesh *mesh = (TMesh *)alloc->MemAlloc( alloc->pUserData, sizeof( TMesh ));
	if (mesh == NULL) {
		return NULL;
	}
	
	if (alloc->nMeshEdgeBucketSize < 16)
		alloc->nMeshEdgeBucketSize = 16;
	if (alloc->nMeshEdgeBucketSize > 4096)
		alloc->nMeshEdgeBucketSize = 4096;
	
	if (alloc->nMeshVertexBucketSize < 16)
		alloc->nMeshVertexBucketSize = 16;
	if (alloc->nMeshVertexBucketSize > 4096)
		alloc->nMeshVertexBucketSize = 4096;
	
	if (alloc->nMeshFaceBucketSize < 16)
		alloc->nMeshFaceBucketSize = 16;
	if (alloc->nMeshFaceBucketSize > 4096)
		alloc->nMeshFaceBucketSize = 4096;

	mesh->pEdgeBucket = createBucketAlloc( alloc, "Mesh Edges", sizeof(EdgePair), alloc->nMeshEdgeBucketSize );
	mesh->pVertexBucket = createBucketAlloc( alloc, "Mesh Vertices", sizeof(TVertex), alloc->nMeshVertexBucketSize );
	mesh->pFaceBucket = createBucketAlloc( alloc, "Mesh Faces", sizeof(TFace), alloc->nMeshFaceBucketSize );

	v = &mesh->vHead;
	f = &mesh->fHead;
	e = &mesh->eHead;
	eSym = &mesh->eHeadSym;

	v->pNext = v->pPrev = v;
	v->pHalfEdge = NULL;

	f->pNext = f->pPrev = f;
	f->pHalfEdge = NULL;
	f->pTrail = NULL;
	f->bMarked = FALSE;
	f->bInside = FALSE;

	e->pNext = e;
	e->Sym = eSym;
	e->Onext = NULL;
	e->Lnext = NULL;
	e->pOrigin = NULL;
	e->Lface = NULL;
	e->nWinding = 0;
	e->pActiveRegion = NULL;

	eSym->pNext = eSym;
	eSym->Sym = e;
	eSym->Onext = NULL;
	eSym->Lnext = NULL;
	eSym->pOrigin = NULL;
	eSym->Lface = NULL;
	eSym->nWinding = 0;
	eSym->pActiveRegion = NULL;

	return mesh;
}


/* tessMeshUnion( mesh1, mesh2 ) forms the union of all structures in
* both meshes, and returns the new mesh (the old meshes are destroyed).
*/
TMesh *tessMeshUnion( TAlloc* alloc, TMesh *mesh1, TMesh *mesh2 )
{
	TFace *f1 = &mesh1->fHead;
	TVertex *v1 = &mesh1->vHead;
	THalfEdge *e1 = &mesh1->eHead;
	TFace *f2 = &mesh2->fHead;
	TVertex *v2 = &mesh2->vHead;
	THalfEdge *e2 = &mesh2->eHead;

	/* Add the faces, vertices, and edges of mesh2 to those of mesh1 */
	if( f2->pNext != f2 ) {
		f1->pPrev->pNext = f2->pNext;
		f2->pNext->pPrev = f1->pPrev;
		f2->pPrev->pNext = f1;
		f1->pPrev = f2->pPrev;
	}

	if( v2->pNext != v2 ) {
		v1->pPrev->pNext = v2->pNext;
		v2->pNext->pPrev = v1->pPrev;
		v2->pPrev->pNext = v1;
		v1->pPrev = v2->pPrev;
	}

	if( e2->pNext != e2 ) {
		e1->Sym->pNext->Sym->pNext = e2->pNext;
		e2->pNext->Sym->pNext = e1->Sym->pNext;
		e2->Sym->pNext->Sym->pNext = e1;
		e1->Sym->pNext = e2->Sym->pNext;
	}

	alloc->MemFree( alloc->pUserData, mesh2 );
	return mesh1;
}


static int CountFaceVerts( TFace *f )
{
	THalfEdge *eCur = f->pHalfEdge;
	int n = 0;
	do
	{
		n++;
		eCur = eCur->Lnext;
	}
	while (eCur != f->pHalfEdge);
	return n;
}

int tessMeshMergeConvexFaces( TMesh *mesh, int maxVertsPerFace )
{
	TFace *f;
	THalfEdge *eCur, *eNext, *eSym;
	TVertex *vStart;
	int curNv, symNv;
	
	for( f = mesh->fHead.pNext; f != &mesh->fHead; f = f->pNext )
	{
		// Skip faces which are outside the result.
		if( !f->bInside )
			continue;

		eCur = f->pHalfEdge;
		vStart = eCur->pOrigin;
			
		while (1)
		{
			eNext = eCur->Lnext;
			eSym = eCur->Sym;

			// Try to merge if the neighbour face is valid.
			if( eSym && eSym->Lface && eSym->Lface->bInside )
			{
				// Try to merge the neighbour faces if the resulting polygons
				// does not exceed maximum number of vertices.
				curNv = CountFaceVerts( f );
				symNv = CountFaceVerts( eSym->Lface );
				if( (curNv+symNv-2) <= maxVertsPerFace )
				{
					// Merge if the resulting poly is convex.
					if( VertCCW( eCur->Lprev->pOrigin, eCur->pOrigin, eSym->Lnext->Lnext->pOrigin ) &&
						VertCCW( eSym->Lprev->pOrigin, eSym->pOrigin, eCur->Lnext->Lnext->pOrigin ) )
					{
						eNext = eSym->Lnext;
						if( !tessMeshDelete( mesh, eSym ) )
							return 0;
						eCur = 0;
					}
				}
			}
			
			if( eCur && eCur->Lnext->pOrigin == vStart )
				break;
				
			// Continue to next edge.
			eCur = eNext;
		}
	}
	
	return 1;
}


#ifdef DELETE_BY_ZAPPING

/* tessMeshDeleteMesh( mesh ) will free all storage for any valid mesh.
*/
void tessMeshDeleteMesh( TAlloc* alloc, TMesh *mesh )
{
	TFace *fHead = &mesh->fHead;

	while( fHead->pNext != fHead ) {
		tessMeshZapFace( fHead->pNext );
	}
	assert( mesh->vHead.pNext == &mesh->vHead );

	alloc->MemFree( alloc->pUserData, mesh );
}

#else

/* tessMeshDeleteMesh( mesh ) will free all storage for any valid mesh.
*/
void tessMeshDeleteMesh( TAlloc* alloc, TMesh *mesh )
{
	deleteBucketAlloc(mesh->pEdgeBucket);
	deleteBucketAlloc(mesh->pVertexBucket);
	deleteBucketAlloc(mesh->pFaceBucket);

	alloc->MemFree( alloc->pUserData, mesh );
}

#endif

#ifndef NDEBUG

/* tessMeshCheckMesh( mesh ) checks a mesh for self-consistency.
*/
void tessMeshCheckMesh( TMesh *mesh )
{
	TFace *fHead = &mesh->fHead;
	TVertex *vHead = &mesh->vHead;
	THalfEdge *eHead = &mesh->eHead;
	TFace *f, *fPrev;
	TVertex *v, *vPrev;
	THalfEdge *e, *ePrev;

	fPrev = fHead;
	for( fPrev = fHead ; (f = fPrev->pNext) != fHead; fPrev = f) {
		assert( f->pPrev == fPrev );
		e = f->pHalfEdge;
		do {
			assert( e->Sym != e );
			assert( e->Sym->Sym == e );
			assert( e->Lnext->Onext->Sym == e );
			assert( e->Onext->Sym->Lnext == e );
			assert( e->Lface == f );
			e = e->Lnext;
		} while( e != f->pHalfEdge );
	}
	assert( f->pPrev == fPrev && f->pHalfEdge == NULL );

	vPrev = vHead;
	for( vPrev = vHead ; (v = vPrev->pNext) != vHead; vPrev = v) {
		assert( v->pPrev == vPrev );
		e = v->pHalfEdge;
		do {
			assert( e->Sym != e );
			assert( e->Sym->Sym == e );
			assert( e->Lnext->Onext->Sym == e );
			assert( e->Onext->Sym->Lnext == e );
			assert( e->pOrigin == v );
			e = e->Onext;
		} while( e != v->pHalfEdge );
	}
	assert( v->pPrev == vPrev && v->pHalfEdge == NULL );

	ePrev = eHead;
	for( ePrev = eHead ; (e = ePrev->pNext) != eHead; ePrev = e) {
		assert( e->Sym->pNext == ePrev->Sym );
		assert( e->Sym != e );
		assert( e->Sym->Sym == e );
		assert( e->pOrigin != NULL );
		assert( e->Dst != NULL );
		assert( e->Lnext->Onext->Sym == e );
		assert( e->Onext->Sym->Lnext == e );
	}
	assert( e->Sym->pNext == ePrev->Sym
		&& e->Sym == &mesh->eHeadSym
		&& e->Sym->Sym == e
		&& e->pOrigin == NULL && e->Dst == NULL
		&& e->Lface == NULL && e->Rface == NULL );
}

#endif
