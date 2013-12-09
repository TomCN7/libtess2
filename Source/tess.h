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

#ifndef TESS_H
#define TESS_H

#include <setjmp.h>
#include "bucketalloc.h"
#include "mesh.h"
#include "dict.h"
#include "priorityq.h"
#include "../Include/tesselator.h"

#ifdef __cplusplus
extern "C" {
#endif

//typedef struct TESStesselator TESStesselator;

struct TTesselator 
{

	/*** state needed for collecting the input data ***/
	TMesh*  pMesh;		/* stores the input contours, and eventually
						the tessellation itself */
	int     nOutOfMemory;

	/*** state needed for projecting onto the sweep plane ***/

	float   fNormal[3];	/* user-specified normal (if provided) */
	float   fsUnit[3];	/* unit vector in s-direction (debugging) */
	float   ftUnit[3];	/* unit vector in t-direction (debugging) */

	float   fBMin[2];
	float   fBMax[2];

	/*** state needed for the line sweep ***/
	int	    nWindingRule;	/* rule for determining polygon interior */

	TDict*  pDict;		/* edge dictionary for sweep line */
	TPriorityQ* pq;		/* priority queue of vertex events */
	TVertex* pVEvent;		/* current sweep event being processed */

	TBucketAlloc* pRegionPool;

	int nVertexIndexCounter;
	
	float*  pVertices;
	int*    pVertexIndices;
	int     nVertexCount;
	int*    pElements;
	int     nElementCount;

	TAlloc  Alloc;
	
	jmp_buf env;			/* place to jump to when memAllocs fail */
};

#ifdef __cplusplus
};
#endif

#endif
