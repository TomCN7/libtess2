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

#define TRUE 1
#define FALSE 0

#ifdef FOR_TRITE_TEST_PROGRAM
extern void DebugEvent( TTesselator *tess );
#else
#define DebugEvent( tess )
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

static void SweepEvent( TTesselator *tess, TVertex *vEvent );
static void WalkDirtyRegions( TTesselator *tess, ActiveRegion *regUp );
static int CheckForRightSplice( TTesselator *tess, ActiveRegion *regUp );

static int EdgeLeq( TTesselator *tess, ActiveRegion *reg1, ActiveRegion *reg2 )
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
{
	TVertex *event = tess->pEvent;
	THalfEdge *e1, *e2;
	float t1, t2;

	e1 = reg1->eUp;
	e2 = reg2->eUp;

	if( e1->Dst == event ) {
		if( e2->Dst == event ) {
			/* Two edges right of the sweep line which meet at the sweep event.
			* Sort them by slope.
			*/
			if( VertLeq( e1->pOrigin, e2->pOrigin )) {
				return EdgeSign( e2->Dst, e1->pOrigin, e2->pOrigin ) <= 0;
			}
			return EdgeSign( e1->Dst, e2->pOrigin, e1->pOrigin ) >= 0;
		}
		return EdgeSign( e2->Dst, event, e2->pOrigin ) <= 0;
	}
	if( e2->Dst == event ) {
		return EdgeSign( e1->Dst, event, e1->pOrigin ) >= 0;
	}

	/* General case - compute signed distance *from* e1, e2 to event */
	t1 = EdgeEval( e1->Dst, event, e1->pOrigin );
	t2 = EdgeEval( e2->Dst, event, e2->pOrigin );
	return (t1 >= t2);
}


static void DeleteRegion( TTesselator *tess, ActiveRegion *reg )
{
	if( reg->fixUpperEdge ) {
		/* It was created with zero winding number, so it better be
		* deleted with zero winding number (ie. it better not get merged
		* with a real edge).
		*/
		assert( reg->eUp->nWinding == 0 );
	}
	reg->eUp->pActiveRegion = NULL;
	dictDelete( tess->pDict, reg->nodeUp );
	bucketFree( tess->pRegionPool, reg );
}


static int FixUpperEdge( TTesselator *tess, ActiveRegion *reg, THalfEdge *newEdge )
/*
* Replace an upper edge which needs fixing (see ConnectRightVertex).
*/
{
	assert( reg->fixUpperEdge );
	if ( !tessMeshDelete( tess->pMesh, reg->eUp ) ) return 0;
	reg->fixUpperEdge = FALSE;
	reg->eUp = newEdge;
	newEdge->pActiveRegion = reg;

	return 1; 
}

static ActiveRegion *TopLeftRegion( TTesselator *tess, ActiveRegion *reg )
{
	TVertex *org = reg->eUp->pOrigin;
	THalfEdge *e;

	/* Find the region above the uppermost edge with the same origin */
	do {
		reg = RegionAbove( reg );
	} while( reg->eUp->pOrigin == org );

	/* If the edge above was a temporary edge introduced by ConnectRightVertex,
	* now is the time to fix it.
	*/
	if( reg->fixUpperEdge ) {
		e = tessMeshConnect( tess->pMesh, RegionBelow(reg)->eUp->Sym, reg->eUp->Lnext );
		if (e == NULL) return NULL;
		if ( !FixUpperEdge( tess, reg, e ) ) return NULL;
		reg = RegionAbove( reg );
	}
	return reg;
}

static ActiveRegion *TopRightRegion( ActiveRegion *reg )
{
	TVertex *dst = reg->eUp->Dst;

	/* Find the region above the uppermost edge with the same destination */
	do {
		reg = RegionAbove( reg );
	} while( reg->eUp->Dst == dst );
	return reg;
}

static ActiveRegion *AddRegionBelow( TTesselator *tess,
									ActiveRegion *regAbove,
									THalfEdge *eNewUp )
/*
* Add a new active region to the sweep line, *somewhere* below "regAbove"
* (according to where the new edge belongs in the sweep-line dictionary).
* The upper edge of the new region will be "eNewUp".
* Winding number and "inside" flag are not updated.
*/
{
	ActiveRegion *regNew = (ActiveRegion *)bucketAlloc( tess->pRegionPool );
	if (regNew == NULL) longjmp(tess->env,1);

	regNew->eUp = eNewUp;
	regNew->nodeUp = dictInsertBefore( tess->pDict, regAbove->nodeUp, regNew );
	if (regNew->nodeUp == NULL) longjmp(tess->env,1);
	regNew->fixUpperEdge = FALSE;
	regNew->sentinel = FALSE;
	regNew->dirty = FALSE;

	eNewUp->pActiveRegion = regNew;
	return regNew;
}

static int IsWindingInside( TTesselator *tess, int n )
{
	switch( tess->nWindingRule ) {
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
	assert( FALSE );
	/*NOTREACHED*/

	return( FALSE );
}


static void ComputeWinding( TTesselator *tess, ActiveRegion *reg )
{
	reg->windingNumber = RegionAbove(reg)->windingNumber + reg->eUp->nWinding;
	reg->inside = IsWindingInside( tess, reg->windingNumber );
}


static void FinishRegion( TTesselator *tess, ActiveRegion *reg )
/*
* Delete a region from the sweep line.  This happens when the upper
* and lower chains of a region meet (at a vertex on the sweep line).
* The "inside" flag is copied to the appropriate mesh face (we could
* not do this before -- since the structure of the mesh is always
* changing, this face may not have even existed until now).
*/
{
	THalfEdge *e = reg->eUp;
	TFace *f = e->Lface;

	f->bInside = reg->inside;
	f->pHalfEdge = e;   /* optimization for tessMeshTessellateMonoRegion() */
	DeleteRegion( tess, reg );
}


static THalfEdge *FinishLeftRegions( TTesselator *tess,
									  ActiveRegion *regFirst, ActiveRegion *regLast )
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
{
	ActiveRegion *reg, *regPrev;
	THalfEdge *e, *ePrev;

	regPrev = regFirst;
	ePrev = regFirst->eUp;
	while( regPrev != regLast ) {
		regPrev->fixUpperEdge = FALSE;	/* placement was OK */
		reg = RegionBelow( regPrev );
		e = reg->eUp;
		if( e->pOrigin != ePrev->pOrigin ) {
			if( ! reg->fixUpperEdge ) {
				/* Remove the last left-going edge.  Even though there are no further
				* edges in the dictionary with this origin, there may be further
				* such edges in the mesh (if we are adding left edges to a vertex
				* that has already been processed).  Thus it is important to call
				* FinishRegion rather than just DeleteRegion.
				*/
				FinishRegion( tess, regPrev );
				break;
			}
			/* If the edge below was a temporary edge introduced by
			* ConnectRightVertex, now is the time to fix it.
			*/
			e = tessMeshConnect( tess->pMesh, ePrev->Lprev, e->Sym );
			if (e == NULL) longjmp(tess->env,1);
			if ( !FixUpperEdge( tess, reg, e ) ) longjmp(tess->env,1);
		}

		/* Relink edges so that ePrev->Onext == e */
		if( ePrev->Onext != e ) {
			if ( !tessMeshSplice( tess->pMesh, e->Oprev, e ) ) longjmp(tess->env,1);
			if ( !tessMeshSplice( tess->pMesh, ePrev, e ) ) longjmp(tess->env,1);
		}
		FinishRegion( tess, regPrev );	/* may change reg->eUp */
		ePrev = reg->eUp;
		regPrev = reg;
	}
	return ePrev;
}


static void AddRightEdges( TTesselator *tess, ActiveRegion *regUp,
						  THalfEdge *eFirst, THalfEdge *eLast, THalfEdge *eTopLeft,
						  int cleanUp )
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
{
	ActiveRegion *reg, *regPrev;
	THalfEdge *e, *ePrev;
	int firstTime = TRUE;

	/* Insert the new right-going edges in the dictionary */
	e = eFirst;
	do {
		assert( VertLeq( e->pOrigin, e->Dst ));
		AddRegionBelow( tess, regUp, e->Sym );
		e = e->Onext;
	} while ( e != eLast );

	/* Walk *all* right-going edges from e->Org, in the dictionary order,
	* updating the winding numbers of each region, and re-linking the mesh
	* edges to match the dictionary ordering (if necessary).
	*/
	if( eTopLeft == NULL ) {
		eTopLeft = RegionBelow( regUp )->eUp->Rprev;
	}
	regPrev = regUp;
	ePrev = eTopLeft;
	for( ;; ) {
		reg = RegionBelow( regPrev );
		e = reg->eUp->Sym;
		if( e->pOrigin != ePrev->pOrigin ) break;

		if( e->Onext != ePrev ) {
			/* Unlink e from its current position, and relink below ePrev */
			if ( !tessMeshSplice( tess->pMesh, e->Oprev, e ) ) longjmp(tess->env,1);
			if ( !tessMeshSplice( tess->pMesh, ePrev->Oprev, e ) ) longjmp(tess->env,1);
		}
		/* Compute the winding number and "inside" flag for the new regions */
		reg->windingNumber = regPrev->windingNumber - e->nWinding;
		reg->inside = IsWindingInside( tess, reg->windingNumber );

		/* Check for two outgoing edges with same slope -- process these
		* before any intersection tests (see example in tessComputeInterior).
		*/
		regPrev->dirty = TRUE;
		if( ! firstTime && CheckForRightSplice( tess, regPrev )) {
			AddWinding( e, ePrev );
			DeleteRegion( tess, regPrev );
			if ( !tessMeshDelete( tess->pMesh, ePrev ) ) longjmp(tess->env,1);
		}
		firstTime = FALSE;
		regPrev = reg;
		ePrev = e;
	}
	regPrev->dirty = TRUE;
	assert( regPrev->windingNumber - e->nWinding == reg->windingNumber );

	if( cleanUp ) {
		/* Check for intersections between newly adjacent edges. */
		WalkDirtyRegions( tess, regPrev );
	}
}


static void SpliceMergeVertices( TTesselator *tess, THalfEdge *e1,
								THalfEdge *e2 )
/*
* Two vertices with idential coordinates are combined into one.
* e1->Org is kept, while e2->Org is discarded.
*/
{
	if ( !tessMeshSplice( tess->pMesh, e1, e2 ) ) longjmp(tess->env,1); 
}

static void VertexWeights( TVertex *isect, TVertex *org, TVertex *dst,
						  float *weights )
/*
* Find some weights which describe how the intersection vertex is
* a linear combination of "org" and "dest".  Each of the two edges
* which generated "isect" is allocated 50% of the weight; each edge
* splits the weight between its org and dst according to the
* relative distance to "isect".
*/
{
	float t1 = VertL1dist( org, isect );
	float t2 = VertL1dist( dst, isect );

	weights[0] = (float)0.5 * t2 / (t1 + t2);
	weights[1] = (float)0.5 * t1 / (t1 + t2);
	isect->fCoords[0] += weights[0]*org->fCoords[0] + weights[1]*dst->fCoords[0];
	isect->fCoords[1] += weights[0]*org->fCoords[1] + weights[1]*dst->fCoords[1];
	isect->fCoords[2] += weights[0]*org->fCoords[2] + weights[1]*dst->fCoords[2];
}


static void GetIntersectData( TTesselator *tess, TVertex *isect,
							 TVertex *orgUp, TVertex *dstUp,
							 TVertex *orgLo, TVertex *dstLo )
 /*
 * We've computed a new intersection point, now we need a "data" pointer
 * from the user so that we can refer to this new vertex in the
 * rendering callbacks.
 */
{
	float weights[4];

	isect->fCoords[0] = isect->fCoords[1] = isect->fCoords[2] = 0;
	isect->idx = TESS_UNDEF;
	VertexWeights( isect, orgUp, dstUp, &weights[0] );
	VertexWeights( isect, orgLo, dstLo, &weights[2] );
}

static int CheckForRightSplice( TTesselator *tess, ActiveRegion *regUp )
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
{
	ActiveRegion *regLo = RegionBelow(regUp);
	THalfEdge *eUp = regUp->eUp;
	THalfEdge *eLo = regLo->eUp;

	if( VertLeq( eUp->pOrigin, eLo->pOrigin )) {
		if( EdgeSign( eLo->Dst, eUp->pOrigin, eLo->pOrigin ) > 0 ) return FALSE;

		/* eUp->Org appears to be below eLo */
		if( ! VertEq( eUp->pOrigin, eLo->pOrigin )) {
			/* Splice eUp->Org into eLo */
			if ( tessMeshSplitEdge( tess->pMesh, eLo->Sym ) == NULL) longjmp(tess->env,1);
			if ( !tessMeshSplice( tess->pMesh, eUp, eLo->Oprev ) ) longjmp(tess->env,1);
			regUp->dirty = regLo->dirty = TRUE;

		} else if( eUp->pOrigin != eLo->pOrigin ) {
			/* merge the two vertices, discarding eUp->Org */
			pqDelete( tess->pq, eUp->pOrigin->pqHandle );
			SpliceMergeVertices( tess, eLo->Oprev, eUp );
		}
	} else {
		if( EdgeSign( eUp->Dst, eLo->pOrigin, eUp->pOrigin ) < 0 ) return FALSE;

		/* eLo->Org appears to be above eUp, so splice eLo->Org into eUp */
		RegionAbove(regUp)->dirty = regUp->dirty = TRUE;
		if (tessMeshSplitEdge( tess->pMesh, eUp->Sym ) == NULL) longjmp(tess->env,1);
		if ( !tessMeshSplice( tess->pMesh, eLo->Oprev, eUp ) ) longjmp(tess->env,1);
	}
	return TRUE;
}

static int CheckForLeftSplice( TTesselator *tess, ActiveRegion *regUp )
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
{
	ActiveRegion *regLo = RegionBelow(regUp);
	THalfEdge *eUp = regUp->eUp;
	THalfEdge *eLo = regLo->eUp;
	THalfEdge *e;

	assert( ! VertEq( eUp->Dst, eLo->Dst ));

	if( VertLeq( eUp->Dst, eLo->Dst )) {
		if( EdgeSign( eUp->Dst, eLo->Dst, eUp->pOrigin ) < 0 ) return FALSE;

		/* eLo->Dst is above eUp, so splice eLo->Dst into eUp */
		RegionAbove(regUp)->dirty = regUp->dirty = TRUE;
		e = tessMeshSplitEdge( tess->pMesh, eUp );
		if (e == NULL) longjmp(tess->env,1);
		if ( !tessMeshSplice( tess->pMesh, eLo->Sym, e ) ) longjmp(tess->env,1);
		e->Lface->bInside = regUp->inside;
	} else {
		if( EdgeSign( eLo->Dst, eUp->Dst, eLo->pOrigin ) > 0 ) return FALSE;

		/* eUp->Dst is below eLo, so splice eUp->Dst into eLo */
		regUp->dirty = regLo->dirty = TRUE;
		e = tessMeshSplitEdge( tess->pMesh, eLo );
		if (e == NULL) longjmp(tess->env,1);    
		if ( !tessMeshSplice( tess->pMesh, eUp->Lnext, eLo->Sym ) ) longjmp(tess->env,1);
		e->Rface->bInside = regUp->inside;
	}
	return TRUE;
}


static int CheckForIntersect( TTesselator *tess, ActiveRegion *regUp )
/*
* Check the upper and lower edges of the given region to see if
* they intersect.  If so, create the intersection and add it
* to the data structures.
*
* Returns TRUE if adding the new intersection resulted in a recursive
* call to AddRightEdges(); in this case all "dirty" regions have been
* checked for intersections, and possibly regUp has been deleted.
*/
{
	ActiveRegion *regLo = RegionBelow(regUp);
	THalfEdge *eUp = regUp->eUp;
	THalfEdge *eLo = regLo->eUp;
	TVertex *orgUp = eUp->pOrigin;
	TVertex *orgLo = eLo->pOrigin;
	TVertex *dstUp = eUp->Dst;
	TVertex *dstLo = eLo->Dst;
	float tMinUp, tMaxLo;
	TVertex isect, *orgMin;
	THalfEdge *e;

	assert( ! VertEq( dstLo, dstUp ));
	assert( EdgeSign( dstUp, tess->pEvent, orgUp ) <= 0 );
	assert( EdgeSign( dstLo, tess->pEvent, orgLo ) >= 0 );
	assert( orgUp != tess->pEvent && orgLo != tess->pEvent );
	assert( ! regUp->fixUpperEdge && ! regLo->fixUpperEdge );

	if( orgUp == orgLo ) return FALSE;	/* right endpoints are the same */

	tMinUp = MIN( orgUp->t, dstUp->t );
	tMaxLo = MAX( orgLo->t, dstLo->t );
	if( tMinUp > tMaxLo ) return FALSE;	/* t ranges do not overlap */

	if( VertLeq( orgUp, orgLo )) {
		if( EdgeSign( dstLo, orgUp, orgLo ) > 0 ) return FALSE;
	} else {
		if( EdgeSign( dstUp, orgLo, orgUp ) < 0 ) return FALSE;
	}

	/* At this point the edges intersect, at least marginally */
	DebugEvent( tess );

	tesedgeIntersect( dstUp, orgUp, dstLo, orgLo, &isect );
	/* The following properties are guaranteed: */
	assert( MIN( orgUp->t, dstUp->t ) <= isect.t );
	assert( isect.t <= MAX( orgLo->t, dstLo->t ));
	assert( MIN( dstLo->s, dstUp->s ) <= isect.s );
	assert( isect.s <= MAX( orgLo->s, orgUp->s ));

	if( VertLeq( &isect, tess->pEvent )) {
		/* The intersection point lies slightly to the left of the sweep line,
		* so move it until it''s slightly to the right of the sweep line.
		* (If we had perfect numerical precision, this would never happen
		* in the first place).  The easiest and safest thing to do is
		* replace the intersection by tess->event.
		*/
		isect.s = tess->pEvent->s;
		isect.t = tess->pEvent->t;
	}
	/* Similarly, if the computed intersection lies to the right of the
	* rightmost origin (which should rarely happen), it can cause
	* unbelievable inefficiency on sufficiently degenerate inputs.
	* (If you have the test program, try running test54.d with the
	* "X zoom" option turned on).
	*/
	orgMin = VertLeq( orgUp, orgLo ) ? orgUp : orgLo;
	if( VertLeq( orgMin, &isect )) {
		isect.s = orgMin->s;
		isect.t = orgMin->t;
	}

	if( VertEq( &isect, orgUp ) || VertEq( &isect, orgLo )) {
		/* Easy case -- intersection at one of the right endpoints */
		(void) CheckForRightSplice( tess, regUp );
		return FALSE;
	}

	if(    (! VertEq( dstUp, tess->pEvent )
		&& EdgeSign( dstUp, tess->pEvent, &isect ) >= 0)
		|| (! VertEq( dstLo, tess->pEvent )
		&& EdgeSign( dstLo, tess->pEvent, &isect ) <= 0 ))
	{
		/* Very unusual -- the new upper or lower edge would pass on the
		* wrong side of the sweep event, or through it.  This can happen
		* due to very small numerical errors in the intersection calculation.
		*/
		if( dstLo == tess->pEvent ) {
			/* Splice dstLo into eUp, and process the new region(s) */
			if (tessMeshSplitEdge( tess->pMesh, eUp->Sym ) == NULL) longjmp(tess->env,1);
			if ( !tessMeshSplice( tess->pMesh, eLo->Sym, eUp ) ) longjmp(tess->env,1);
			regUp = TopLeftRegion( tess, regUp );
			if (regUp == NULL) longjmp(tess->env,1);
			eUp = RegionBelow(regUp)->eUp;
			FinishLeftRegions( tess, RegionBelow(regUp), regLo );
			AddRightEdges( tess, regUp, eUp->Oprev, eUp, eUp, TRUE );
			return TRUE;
		}
		if( dstUp == tess->pEvent ) {
			/* Splice dstUp into eLo, and process the new region(s) */
			if (tessMeshSplitEdge( tess->pMesh, eLo->Sym ) == NULL) longjmp(tess->env,1);
			if ( !tessMeshSplice( tess->pMesh, eUp->Lnext, eLo->Oprev ) ) longjmp(tess->env,1); 
			regLo = regUp;
			regUp = TopRightRegion( regUp );
			e = RegionBelow(regUp)->eUp->Rprev;
			regLo->eUp = eLo->Oprev;
			eLo = FinishLeftRegions( tess, regLo, NULL );
			AddRightEdges( tess, regUp, eLo->Onext, eUp->Rprev, e, TRUE );
			return TRUE;
		}
		/* Special case: called from ConnectRightVertex.  If either
		* edge passes on the wrong side of tess->event, split it
		* (and wait for ConnectRightVertex to splice it appropriately).
		*/
		if( EdgeSign( dstUp, tess->pEvent, &isect ) >= 0 ) {
			RegionAbove(regUp)->dirty = regUp->dirty = TRUE;
			if (tessMeshSplitEdge( tess->pMesh, eUp->Sym ) == NULL) longjmp(tess->env,1);
			eUp->pOrigin->s = tess->pEvent->s;
			eUp->pOrigin->t = tess->pEvent->t;
		}
		if( EdgeSign( dstLo, tess->pEvent, &isect ) <= 0 ) {
			regUp->dirty = regLo->dirty = TRUE;
			if (tessMeshSplitEdge( tess->pMesh, eLo->Sym ) == NULL) longjmp(tess->env,1);
			eLo->pOrigin->s = tess->pEvent->s;
			eLo->pOrigin->t = tess->pEvent->t;
		}
		/* leave the rest for ConnectRightVertex */
		return FALSE;
	}

	/* General case -- split both edges, splice into new vertex.
	* When we do the splice operation, the order of the arguments is
	* arbitrary as far as correctness goes.  However, when the operation
	* creates a new face, the work done is proportional to the size of
	* the new face.  We expect the faces in the processed part of
	* the mesh (ie. eUp->Lface) to be smaller than the faces in the
	* unprocessed original contours (which will be eLo->Oprev->Lface).
	*/
	if (tessMeshSplitEdge( tess->pMesh, eUp->Sym ) == NULL) longjmp(tess->env,1);
	if (tessMeshSplitEdge( tess->pMesh, eLo->Sym ) == NULL) longjmp(tess->env,1);
	if ( !tessMeshSplice( tess->pMesh, eLo->Oprev, eUp ) ) longjmp(tess->env,1);
	eUp->pOrigin->s = isect.s;
	eUp->pOrigin->t = isect.t;
	eUp->pOrigin->pqHandle = pqInsert( &tess->Alloc, tess->pq, eUp->pOrigin );
	if (eUp->pOrigin->pqHandle == INV_HANDLE) {
		pqDeletePriorityQ( &tess->Alloc, tess->pq );
		tess->pq = NULL;
		longjmp(tess->env,1);
	}
	GetIntersectData( tess, eUp->pOrigin, orgUp, dstUp, orgLo, dstLo );
	RegionAbove(regUp)->dirty = regUp->dirty = regLo->dirty = TRUE;
	return FALSE;
}

static void WalkDirtyRegions( TTesselator *tess, ActiveRegion *regUp )
/*
* When the upper or lower edge of any region changes, the region is
* marked "dirty".  This routine walks through all the dirty regions
* and makes sure that the dictionary invariants are satisfied
* (see the comments at the beginning of this file).  Of course
* new dirty regions can be created as we make changes to restore
* the invariants.
*/
{
	ActiveRegion *regLo = RegionBelow(regUp);
	THalfEdge *eUp, *eLo;

	for( ;; ) {
		/* Find the lowest dirty region (we walk from the bottom up). */
		while( regLo->dirty ) {
			regUp = regLo;
			regLo = RegionBelow(regLo);
		}
		if( ! regUp->dirty ) {
			regLo = regUp;
			regUp = RegionAbove( regUp );
			if( regUp == NULL || ! regUp->dirty ) {
				/* We've walked all the dirty regions */
				return;
			}
		}
		regUp->dirty = FALSE;
		eUp = regUp->eUp;
		eLo = regLo->eUp;

		if( eUp->Dst != eLo->Dst ) {
			/* Check that the edge ordering is obeyed at the Dst vertices. */
			if( CheckForLeftSplice( tess, regUp )) {

				/* If the upper or lower edge was marked fixUpperEdge, then
				* we no longer need it (since these edges are needed only for
				* vertices which otherwise have no right-going edges).
				*/
				if( regLo->fixUpperEdge ) {
					DeleteRegion( tess, regLo );
					if ( !tessMeshDelete( tess->pMesh, eLo ) ) longjmp(tess->env,1);
					regLo = RegionBelow( regUp );
					eLo = regLo->eUp;
				} else if( regUp->fixUpperEdge ) {
					DeleteRegion( tess, regUp );
					if ( !tessMeshDelete( tess->pMesh, eUp ) ) longjmp(tess->env,1);
					regUp = RegionAbove( regLo );
					eUp = regUp->eUp;
				}
			}
		}
		if( eUp->pOrigin != eLo->pOrigin ) {
			if(    eUp->Dst != eLo->Dst
				&& ! regUp->fixUpperEdge && ! regLo->fixUpperEdge
				&& (eUp->Dst == tess->pEvent || eLo->Dst == tess->pEvent) )
			{
				/* When all else fails in CheckForIntersect(), it uses tess->event
				* as the intersection location.  To make this possible, it requires
				* that tess->event lie between the upper and lower edges, and also
				* that neither of these is marked fixUpperEdge (since in the worst
				* case it might splice one of these edges into tess->event, and
				* violate the invariant that fixable edges are the only right-going
				* edge from their associated vertex).
				*/
				if( CheckForIntersect( tess, regUp )) {
					/* WalkDirtyRegions() was called recursively; we're done */
					return;
				}
			} else {
				/* Even though we can't use CheckForIntersect(), the Org vertices
				* may violate the dictionary edge ordering.  Check and correct this.
				*/
				(void) CheckForRightSplice( tess, regUp );
			}
		}
		if( eUp->pOrigin == eLo->pOrigin && eUp->Dst == eLo->Dst ) {
			/* A degenerate loop consisting of only two edges -- delete it. */
			AddWinding( eLo, eUp );
			DeleteRegion( tess, regUp );
			if ( !tessMeshDelete( tess->pMesh, eUp ) ) longjmp(tess->env,1);
			regUp = RegionAbove( regLo );
		}
	}
}


static void ConnectRightVertex( TTesselator *tess, ActiveRegion *regUp,
							   THalfEdge *eBottomLeft )
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
{
	THalfEdge *eNew;
	THalfEdge *eTopLeft = eBottomLeft->Onext;
	ActiveRegion *regLo = RegionBelow(regUp);
	THalfEdge *eUp = regUp->eUp;
	THalfEdge *eLo = regLo->eUp;
	int degenerate = FALSE;

	if( eUp->Dst != eLo->Dst ) {
		(void) CheckForIntersect( tess, regUp );
	}

	/* Possible new degeneracies: upper or lower edge of regUp may pass
	* through vEvent, or may coincide with new intersection vertex
	*/
	if( VertEq( eUp->pOrigin, tess->pEvent )) {
		if ( !tessMeshSplice( tess->pMesh, eTopLeft->Oprev, eUp ) ) longjmp(tess->env,1);
		regUp = TopLeftRegion( tess, regUp );
		if (regUp == NULL) longjmp(tess->env,1);
		eTopLeft = RegionBelow( regUp )->eUp;
		FinishLeftRegions( tess, RegionBelow(regUp), regLo );
		degenerate = TRUE;
	}
	if( VertEq( eLo->pOrigin, tess->pEvent )) {
		if ( !tessMeshSplice( tess->pMesh, eBottomLeft, eLo->Oprev ) ) longjmp(tess->env,1);
		eBottomLeft = FinishLeftRegions( tess, regLo, NULL );
		degenerate = TRUE;
	}
	if( degenerate ) {
		AddRightEdges( tess, regUp, eBottomLeft->Onext, eTopLeft, eTopLeft, TRUE );
		return;
	}

	/* Non-degenerate situation -- need to add a temporary, fixable edge.
	* Connect to the closer of eLo->Org, eUp->Org.
	*/
	if( VertLeq( eLo->pOrigin, eUp->pOrigin )) {
		eNew = eLo->Oprev;
	} else {
		eNew = eUp;
	}
	eNew = tessMeshConnect( tess->pMesh, eBottomLeft->Lprev, eNew );
	if (eNew == NULL) longjmp(tess->env,1);

	/* Prevent cleanup, otherwise eNew might disappear before we've even
	* had a chance to mark it as a temporary edge.
	*/
	AddRightEdges( tess, regUp, eNew, eNew->Onext, eNew->Onext, FALSE );
	eNew->Sym->pActiveRegion->fixUpperEdge = TRUE;
	WalkDirtyRegions( tess, regUp );
}

/* Because vertices at exactly the same location are merged together
* before we process the sweep event, some degenerate cases can't occur.
* However if someone eventually makes the modifications required to
* merge features which are close together, the cases below marked
* TOLERANCE_NONZERO will be useful.  They were debugged before the
* code to merge identical vertices in the main loop was added.
*/
#define TOLERANCE_NONZERO	FALSE

static void ConnectLeftDegenerate( TTesselator *tess,
								  ActiveRegion *regUp, TVertex *vEvent )
/*
* The event vertex lies exacty on an already-processed edge or vertex.
* Adding the new vertex involves splicing it into the already-processed
* part of the mesh.
*/
{
	THalfEdge *e, *eTopLeft, *eTopRight, *eLast;
	ActiveRegion *reg;

	e = regUp->eUp;
	if( VertEq( e->pOrigin, vEvent )) {
		/* e->Org is an unprocessed vertex - just combine them, and wait
		* for e->Org to be pulled from the queue
		*/
		assert( TOLERANCE_NONZERO );
		SpliceMergeVertices( tess, e, vEvent->pHalfEdge );
		return;
	}

	if( ! VertEq( e->Dst, vEvent )) {
		/* General case -- splice vEvent into edge e which passes through it */
		if (tessMeshSplitEdge( tess->pMesh, e->Sym ) == NULL) longjmp(tess->env,1);
		if( regUp->fixUpperEdge ) {
			/* This edge was fixable -- delete unused portion of original edge */
			if ( !tessMeshDelete( tess->pMesh, e->Onext ) ) longjmp(tess->env,1);
			regUp->fixUpperEdge = FALSE;
		}
		if ( !tessMeshSplice( tess->pMesh, vEvent->pHalfEdge, e ) ) longjmp(tess->env,1);
		SweepEvent( tess, vEvent );	/* recurse */
		return;
	}

	/* vEvent coincides with e->Dst, which has already been processed.
	* Splice in the additional right-going edges.
	*/
	assert( TOLERANCE_NONZERO );
	regUp = TopRightRegion( regUp );
	reg = RegionBelow( regUp );
	eTopRight = reg->eUp->Sym;
	eTopLeft = eLast = eTopRight->Onext;
	if( reg->fixUpperEdge ) {
		/* Here e->Dst has only a single fixable edge going right.
		* We can delete it since now we have some real right-going edges.
		*/
		assert( eTopLeft != eTopRight );   /* there are some left edges too */
		DeleteRegion( tess, reg );
		if ( !tessMeshDelete( tess->pMesh, eTopRight ) ) longjmp(tess->env,1);
		eTopRight = eTopLeft->Oprev;
	}
	if ( !tessMeshSplice( tess->pMesh, vEvent->pHalfEdge, eTopRight ) ) longjmp(tess->env,1);
	if( ! EdgeGoesLeft( eTopLeft )) {
		/* e->Dst had no left-going edges -- indicate this to AddRightEdges() */
		eTopLeft = NULL;
	}
	AddRightEdges( tess, regUp, eTopRight->Onext, eLast, eTopLeft, TRUE );
}


static void ConnectLeftVertex( TTesselator *tess, TVertex *vEvent )
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
{
	ActiveRegion *regUp, *regLo, *reg;
	THalfEdge *eUp, *eLo, *eNew;
	ActiveRegion tmp;

	/* assert( vEvent->anEdge->Onext->Onext == vEvent->anEdge ); */

	/* Get a pointer to the active region containing vEvent */
	tmp.eUp = vEvent->pHalfEdge->Sym;
	/* __GL_DICTLISTKEY */ /* tessDictListSearch */
	regUp = (ActiveRegion *)dictKey( dictSearch( tess->pDict, &tmp ));
	regLo = RegionBelow( regUp );
	if( !regLo ) {
		// This may happen if the input polygon is coplanar.
		return;
	}
	eUp = regUp->eUp;
	eLo = regLo->eUp;

	/* Try merging with U or L first */
	if( EdgeSign( eUp->Dst, vEvent, eUp->pOrigin ) == 0 ) {
		ConnectLeftDegenerate( tess, regUp, vEvent );
		return;
	}

	/* Connect vEvent to rightmost processed vertex of either chain.
	* e->Dst is the vertex that we will connect to vEvent.
	*/
	reg = VertLeq( eLo->Dst, eUp->Dst ) ? regUp : regLo;

	if( regUp->inside || reg->fixUpperEdge) {
		if( reg == regUp ) {
			eNew = tessMeshConnect( tess->pMesh, vEvent->pHalfEdge->Sym, eUp->Lnext );
			if (eNew == NULL) longjmp(tess->env,1);
		} else {
			THalfEdge *tempHalfEdge= tessMeshConnect( tess->pMesh, eLo->Dnext, vEvent->pHalfEdge);
			if (tempHalfEdge == NULL) longjmp(tess->env,1);

			eNew = tempHalfEdge->Sym;
		}
		if( reg->fixUpperEdge ) {
			if ( !FixUpperEdge( tess, reg, eNew ) ) longjmp(tess->env,1);
		} else {
			ComputeWinding( tess, AddRegionBelow( tess, regUp, eNew ));
		}
		SweepEvent( tess, vEvent );
	} else {
		/* The new vertex is in a region which does not belong to the polygon.
		* We don''t need to connect this vertex to the rest of the mesh.
		*/
		AddRightEdges( tess, regUp, vEvent->pHalfEdge, vEvent->pHalfEdge, NULL, TRUE );
	}
}


static void SweepEvent( TTesselator *tess, TVertex *vEvent )
/*
* Does everything necessary when the sweep line crosses a vertex.
* Updates the mesh and the edge dictionary.
*/
{
	ActiveRegion *regUp, *reg;
	THalfEdge *e, *eTopLeft, *eBottomLeft;

	tess->pEvent = vEvent;		/* for access in EdgeLeq() */
	DebugEvent( tess );

	/* Check if this vertex is the right endpoint of an edge that is
	* already in the dictionary.  In this case we don't need to waste
	* time searching for the location to insert new edges.
	*/
	e = vEvent->pHalfEdge;
	while( e->pActiveRegion == NULL ) {
		e = e->Onext;
		if( e == vEvent->pHalfEdge ) {
			/* All edges go right -- not incident to any processed edges */
			ConnectLeftVertex( tess, vEvent );
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
	regUp = TopLeftRegion( tess, e->pActiveRegion );
	if (regUp == NULL) longjmp(tess->env,1);
	reg = RegionBelow( regUp );
	eTopLeft = reg->eUp;
	eBottomLeft = FinishLeftRegions( tess, reg, NULL );

	/* Next we process all the right-going edges from vEvent.  This
	* involves adding the edges to the dictionary, and creating the
	* associated "active regions" which record information about the
	* regions between adjacent dictionary edges.
	*/
	if( eBottomLeft->Onext == eTopLeft ) 
	{
		/* No right-going edges -- add a temporary "fixable" edge */
		ConnectRightVertex( tess, regUp, eBottomLeft );
	} else {
		AddRightEdges( tess, regUp, eBottomLeft->Onext, eTopLeft, eTopLeft, TRUE );
	}
}


/* Make the sentinel coordinates big enough that they will never be
* merged with real input features.
*/

static void AddSentinel( TTesselator *tess, float smin, float smax, float t )
/*
* We add two sentinel edges above and below all other edges,
* to avoid special cases at the top and bottom.
*/
{
	THalfEdge *e;
	ActiveRegion *reg = (ActiveRegion *)bucketAlloc( tess->pRegionPool );
	if (reg == NULL) longjmp(tess->env,1);

	e = tessMeshMakeEdge( tess->pMesh );
	if (e == NULL) longjmp(tess->env,1);

	e->pOrigin->s = smax;
	e->pOrigin->t = t;
	e->Dst->s = smin;
	e->Dst->t = t;
	tess->pEvent = e->Dst;		/* initialize it */

	reg->eUp = e;
	reg->windingNumber = 0;
	reg->inside = FALSE;
	reg->fixUpperEdge = FALSE;
	reg->sentinel = TRUE;
	reg->dirty = FALSE;
	reg->nodeUp = dictInsert( tess->pDict, reg );
	if (reg->nodeUp == NULL) longjmp(tess->env,1);
}


static void InitEdgeDict( TTesselator *tess )
/*
* We maintain an ordering of edge intersections with the sweep line.
* This order is maintained in a dynamic dictionary.
*/
{
	float w, h;
	float smin, smax, tmin, tmax;

	tess->pDict = dictNewDict( &tess->Alloc, tess, (int (*)(void *, TDictKey, TDictKey)) EdgeLeq );
	if (tess->pDict == NULL) longjmp(tess->env,1);

	w = (tess->fBMax[0] - tess->fBMin[0]);
	h = (tess->fBMax[1] - tess->fBMin[1]);

	smin = tess->fBMin[0] - w;
	smax = tess->fBMax[0] + w;
	tmin = tess->fBMin[1] - h;
	tmax = tess->fBMax[1] + h;

	AddSentinel( tess, smin, smax, tmin );
	AddSentinel( tess, smin, smax, tmax );
}


static void DoneEdgeDict( TTesselator *tess )
{
	ActiveRegion *reg;
	int fixedEdges = 0;

	while( (reg = (ActiveRegion *)dictKey( dictMin( tess->pDict ))) != NULL ) {
		/*
		* At the end of all processing, the dictionary should contain
		* only the two sentinel edges, plus at most one "fixable" edge
		* created by ConnectRightVertex().
		*/
		if( ! reg->sentinel ) {
			assert( reg->fixUpperEdge );
			assert( ++fixedEdges == 1 );
		}
		assert( reg->windingNumber == 0 );
		DeleteRegion( tess, reg );
		/*    tessMeshDelete( reg->eUp );*/
	}
	dictDeleteDict( &tess->Alloc, tess->pDict );
}


static void RemoveDegenerateEdges( TTesselator *tess )
/*
* Remove zero-length edges, and contours with fewer than 3 vertices.
*/
{
	THalfEdge *e, *eNext, *eLnext;
	THalfEdge *eHead = &tess->pMesh->eHead;

	/*LINTED*/
	for( e = eHead->pNext; e != eHead; e = eNext ) {
		eNext = e->pNext;
		eLnext = e->Lnext;

		if( VertEq( e->pOrigin, e->Dst ) && e->Lnext->Lnext != e ) {
			/* Zero-length edge, contour has at least 3 edges */

			SpliceMergeVertices( tess, eLnext, e );	/* deletes e->Org */
			if ( !tessMeshDelete( tess->pMesh, e ) ) longjmp(tess->env,1); /* e is a self-loop */
			e = eLnext;
			eLnext = e->Lnext;
		}
		if( eLnext->Lnext == e ) {
			/* Degenerate contour (one or two edges) */

			if( eLnext != e ) {
				if( eLnext == eNext || eLnext == eNext->Sym ) { eNext = eNext->pNext; }
				if ( !tessMeshDelete( tess->pMesh, eLnext ) ) longjmp(tess->env,1);
			}
			if( e == eNext || e == eNext->Sym ) { eNext = eNext->pNext; }
			if ( !tessMeshDelete( tess->pMesh, e ) ) longjmp(tess->env,1);
		}
	}
}

static int InitPriorityQ( TTesselator *tess )
/*
* Insert all vertices into the priority queue which determines the
* order in which vertices cross the sweep line.
*/
{
	TPriorityQ *pq;
	TVertex *v, *vHead;
	int vertexCount = 0;
	
	vHead = &tess->pMesh->vHead;
	for( v = vHead->pNext; v != vHead; v = v->pNext ) {
		vertexCount++;
	}
	/* Make sure there is enough space for sentinels. */
	vertexCount += MAX( 8, tess->Alloc.nExtraVertices );
	
	pq = tess->pq = pqNewPriorityQ( &tess->Alloc, vertexCount, (int (*)(PQkey, PQkey)) tesvertLeq );
	if (pq == NULL) return 0;

	vHead = &tess->pMesh->vHead;
	for (v = vHead->pNext; v != vHead; v = v->pNext)
    {
		v->pqHandle = pqInsert(&tess->Alloc, pq, v);
		if (v->pqHandle == INV_HANDLE)
			break;
	}
	if (v != vHead || !pqInit(&tess->Alloc, pq)) 
    {
		pqDeletePriorityQ(&tess->Alloc, tess->pq);
		tess->pq = NULL;
		return 0;
	}

	return 1;
}


static void DonePriorityQ( TTesselator *tess )
{
	pqDeletePriorityQ( &tess->Alloc, tess->pq );
}


static int RemoveDegenerateFaces( TTesselator *tess, TMesh *mesh )
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
{
	TFace *f, *fNext;
	THalfEdge *e;

	/*LINTED*/
	for( f = mesh->fHead.pNext; f != &mesh->fHead; f = fNext ) {
		fNext = f->pNext;
		e = f->pHalfEdge;
		assert( e->Lnext != e );

		if( e->Lnext->Lnext == e ) {
			/* A face with only two edges */
			AddWinding( e->Onext, e );
			if ( !tessMeshDelete( tess->pMesh, e ) ) return 0;
		}
	}
	return 1;
}

int tessComputeInterior( TTesselator *tess )
/*
* tessComputeInterior( tess ) computes the planar arrangement specified
* by the given contours, and further subdivides this arrangement
* into regions.  Each region is marked "inside" if it belongs
* to the polygon, according to the rule given by tess->windingRule.
* Each interior region is guaranteed be monotone.
*/
{
	TVertex *v, *vNext;

	/* Each vertex defines an event for our sweep line.  Start by inserting
	* all the vertices in a priority queue.  Events are processed in
	* lexicographic order, ie.
	*
	*	e1 < e2  iff  e1.x < e2.x || (e1.x == e2.x && e1.y < e2.y)
	*/
	RemoveDegenerateEdges( tess );
	if ( !InitPriorityQ( tess ) ) return 0; /* if error */
	InitEdgeDict( tess );

	while( (v = (TVertex *)pqExtractMin( tess->pq )) != NULL ) {
		for( ;; ) {
			vNext = (TVertex *)pqMinimum( tess->pq );
			if( vNext == NULL || ! VertEq( vNext, v )) break;

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
			vNext = (TVertex *)pqExtractMin( tess->pq );
			SpliceMergeVertices( tess, v->pHalfEdge, vNext->pHalfEdge );
		}
		SweepEvent( tess, v );
	}

	/* Set tess->event for debugging purposes */
	tess->pEvent = ((ActiveRegion *) dictKey( dictMin( tess->pDict )))->eUp->pOrigin;
	DebugEvent( tess );
	DoneEdgeDict( tess );
	DonePriorityQ( tess );

	if ( !RemoveDegenerateFaces( tess, tess->pMesh ) ) return 0;
	tessMeshCheckMesh( tess->pMesh );

	return 1;
}
