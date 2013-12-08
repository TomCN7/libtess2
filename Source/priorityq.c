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
#include "../Include/tesselator.h"
#include "priorityq.h"


#define INIT_SIZE	32

#define TRUE 1
#define FALSE 0

#ifdef FOR_TRITE_TEST_PROGRAM
#define LEQ(x,y)	(*pq->leq)(x,y)
#else
/* Violates modularity, but a little faster */
#include "geom.h"
#define LEQ(x,y)	VertLeq((TVertex *)x, (TVertex *)y)
#endif


/* Include all the code for the regular heap-based queue here. */

/* The basic operations are insertion of a new key (pqInsert),
* and examination/extraction of a key whose value is minimum
* (pqMinimum/pqExtractMin).  Deletion is also allowed (pqDelete);
* for this purpose pqInsert returns a "handle" which is supplied
* as the argument.
*
* An initial heap may be created efficiently by calling pqInsert
* repeatedly, then calling pqInit.  In any case pqInit must be called
* before any operations other than pqInsert are used.
*
* If the heap is empty, pqMinimum/pqExtractMin will return a NULL key.
* This may also be tested with pqIsEmpty.
*/


/* Since we support deletion the data structure is a little more
* complicated than an ordinary heap.  "nodes" is the heap itself;
* active nodes are stored in the range 1..pq->size.  When the
* heap exceeds its allocated size (pq->max), its size doubles.
* The children of node i are nodes 2i and 2i+1.
*
* Each node stores an index into an array "handles".  Each handle
* stores a key, plus a pointer back to the node which currently
* represents that key (ie. nodes[handles[i].node].handle == i).
*/


#define pqHeapMinimum(pq)	((pq)->pHandles[(pq)->pNodes[1].handle].key)
#define pqHeapIsEmpty(pq)	((pq)->nSize == 0)



/* really pqHeapNewPriorityQHeap */
TPriorityQHeap *pqHeapNewPriorityQ (TAlloc* alloc, int size, int (*leq)(PQkey key1, PQkey key2)) 
{
	TPriorityQHeap *pq = (TPriorityQHeap *)alloc->MemAlloc (alloc->pUserData, sizeof (TPriorityQHeap) );
	if (pq == NULL) return NULL;

	pq->nSize = 0;
	pq->nMax = size;
	pq->pNodes = (PQnode *)alloc->MemAlloc (alloc->pUserData, (size + 1) * sizeof(pq->pNodes[0])) ;
	if (pq->pNodes == NULL) {
		alloc->MemFree (alloc->pUserData, pq) ;
		return NULL;
	}

	pq->pHandles = (PQhandleElem *)alloc->MemAlloc (alloc->pUserData, (size + 1) * sizeof(pq->pHandles[0])) ;
	if (pq->pHandles == NULL) {
		alloc->MemFree (alloc->pUserData, pq->pNodes) ;
		alloc->MemFree (alloc->pUserData, pq) ;
		return NULL;
	}

	pq->nInitialized = FALSE;
	pq->FreeList = 0;
	pq->leq = leq;

	pq->pNodes[1].handle = 1;	/* so that Minimum() returns NULL */
	pq->pHandles[1].key = NULL;
	return pq;
}

/* really pqHeapDeletePriorityQHeap */
void pqHeapDeletePriorityQ (TAlloc* alloc, TPriorityQHeap *pq) 
{
	alloc->MemFree (alloc->pUserData, pq->pHandles) ;
	alloc->MemFree (alloc->pUserData, pq->pNodes) ;
	alloc->MemFree (alloc->pUserData, pq) ;
}


static void FloatDown (TPriorityQHeap *pq, int curr) 
{
	PQnode *n = pq->pNodes;
	PQhandleElem *h = pq->pHandles;
	PQhandle hCurr, hChild;
	int child;

	hCurr = n[curr].handle;
	for (;;)  {
		child = curr << 1;
		if (child < pq->nSize && LEQ (h[n[child+1].handle].key,
			h[n[child].handle].key) ) {
				++child;
		}

		assert(child <= pq->nMax);

		hChild = n[child].handle;
		if (child > pq->nSize || LEQ (h[hCurr].key, h[hChild].key) ) {
			n[curr].handle = hCurr;
			h[hCurr].node = curr;
			break;
		}
		n[curr].handle = hChild;
		h[hChild].node = curr;
		curr = child;
	}
}


static void FloatUp (TPriorityQHeap *pq, int curr) 
{
	PQnode *n = pq->pNodes;
	PQhandleElem *h = pq->pHandles;
	PQhandle hCurr, hParent;
	int parent;

	hCurr = n[curr].handle;
	for (;;)  {
		parent = curr >> 1;
		hParent = n[parent].handle;
		if (parent == 0 || LEQ (h[hParent].key, h[hCurr].key) ) {
			n[curr].handle = hCurr;
			h[hCurr].node = curr;
			break;
		}
		n[curr].handle = hParent;
		h[hParent].node = curr;
		curr = parent;
	}
}

/* really pqHeapInit */
void pqHeapInit (TPriorityQHeap *pq) 
{
	int i;

	/* This method of building a heap is O(n), rather than O(n lg n). */

	for (i = pq->nSize; i >= 1; --i)  {
		FloatDown (pq, i) ;
	}
	pq->nInitialized = TRUE;
}

/* really pqHeapInsert */
/* returns INV_HANDLE iff out of memory */
PQhandle pqHeapInsert (TAlloc* alloc, TPriorityQHeap *pq, PQkey keyNew) 
{
	int curr;
	PQhandle free;

	curr = ++ pq->nSize;
	if ((curr*2) > pq->nMax)  {
		if (!alloc->MemRealloc)
		{
			return INV_HANDLE;
		}
		else
		{
			PQnode *saveNodes= pq->pNodes;
			PQhandleElem *saveHandles= pq->pHandles;

			// If the heap overflows, double its size.
			pq->nMax <<= 1;
			pq->pNodes = (PQnode *)alloc->MemRealloc (alloc->pUserData, pq->pNodes, 
				(size_t)((pq->nMax + 1) * sizeof (pq->pNodes[0]) ));
			if (pq->pNodes == NULL) {
				pq->pNodes = saveNodes;	// restore ptr to free upon return 
				return INV_HANDLE;
			}
			pq->pHandles = (PQhandleElem *)alloc->MemRealloc (alloc->pUserData, pq->pHandles,
				(size_t) ((pq->nMax + 1) * sizeof (pq->pHandles[0]) ));
			if (pq->pHandles == NULL) {
				pq->pHandles = saveHandles; // restore ptr to free upon return 
				return INV_HANDLE;
			}
		}
	}

	if (pq->FreeList == 0)  {
		free = curr;
	} else {
		free = pq->FreeList;
		pq->FreeList = pq->pHandles[free].node;
	}

	pq->pNodes[curr].handle = free;
	pq->pHandles[free].node = curr;
	pq->pHandles[free].key = keyNew;

	if (pq->nInitialized)  {
		FloatUp (pq, curr) ;
	}
	assert(free != INV_HANDLE);
	return free;
}

/* really pqHeapExtractMin */
PQkey pqHeapExtractMin (TPriorityQHeap *pq) 
{
	PQnode *n = pq->pNodes;
	PQhandleElem *h = pq->pHandles;
	PQhandle hMin = n[1].handle;
	PQkey min = h[hMin].key;

	if (pq->nSize > 0)  {
		n[1].handle = n[pq->nSize].handle;
		h[n[1].handle].node = 1;

		h[hMin].key = NULL;
		h[hMin].node = pq->FreeList;
		pq->FreeList = hMin;

		if (-- pq->nSize > 0)  {
			FloatDown (pq, 1) ;
		}
	}
	return min;
}

/* really pqHeapDelete */
void pqHeapDelete (TPriorityQHeap *pq, PQhandle hCurr) 
{
	PQnode *n = pq->pNodes;
	PQhandleElem *h = pq->pHandles;
	int curr;

	assert (hCurr >= 1 && hCurr <= pq->nMax && h[hCurr].key != NULL) ;

	curr = h[hCurr].node;
	n[curr].handle = n[pq->nSize].handle;
	h[n[curr].handle].node = curr;

	if (curr <= -- pq->nSize)  {
		if (curr <= 1 || LEQ (h[n[curr>>1].handle].key, h[n[curr].handle].key) ) {
			FloatDown (pq, curr) ;
		} else {
			FloatUp (pq, curr) ;
		}
	}
	h[hCurr].key = NULL;
	h[hCurr].node = pq->FreeList;
	pq->FreeList = hCurr;
}



/* Now redefine all the function names to map to their "Sort" versions. */

/* really tessPqSortNewPriorityQ */
TPriorityQ *pqNewPriorityQ (TAlloc* alloc, int size, int (*leq)(PQkey key1, PQkey key2)) 
{
	TPriorityQ *pq = (TPriorityQ *)alloc->MemAlloc (alloc->pUserData, sizeof (TPriorityQ) );
	if (pq == NULL) return NULL;

	pq->pHeap = pqHeapNewPriorityQ (alloc, size, leq) ;
	if (pq->pHeap == NULL) {
		alloc->MemFree (alloc->pUserData, pq) ;
		return NULL;
	}

//	pq->keys = (PQkey *)memAlloc (INIT_SIZE * sizeof(pq->keys[0])) ;
	pq->pKeys = (PQkey *)alloc->MemAlloc (alloc->pUserData, size * sizeof(pq->pKeys[0])) ;
	if (pq->pKeys == NULL) {
		pqHeapDeletePriorityQ (alloc, pq->pHeap) ;
		alloc->MemFree (alloc->pUserData, pq) ;
		return NULL;
	}

	pq->Size = 0;
	pq->Max = size; //INIT_SIZE;
	pq->nInitialized = FALSE;
	pq->leq = leq;
	
	return pq;
}

/* really tessPqSortDeletePriorityQ */
void pqDeletePriorityQ (TAlloc* alloc, TPriorityQ *pq) 
{
	assert(pq != NULL); 
	if (pq->pHeap != NULL) pqHeapDeletePriorityQ (alloc, pq->pHeap) ;
	if (pq->ppOrder != NULL) alloc->MemFree (alloc->pUserData, pq->ppOrder) ;
	if (pq->pKeys != NULL) alloc->MemFree (alloc->pUserData, pq->pKeys) ;
	alloc->MemFree (alloc->pUserData, pq) ;
}


#define LT(x,y)     (! LEQ(y,x))
#define GT(x,y)     (! LEQ(x,y))
#define Swap(a,b)   if(1){PQkey *tmp = *a; *a = *b; *b = tmp;}else

/* really tessPqSortInit */
int pqInit (TAlloc* alloc, TPriorityQ *pq) 
{
	PQkey **p, **r, **i, **j, *piv;
	struct { PQkey **p, **r; } Stack[50], *top = Stack;
	unsigned int seed = 2016473283;

	/* Create an array of indirect pointers to the keys, so that we
	* the handles we have returned are still valid.
	*/
	/*
	pq->order = (PQkey **)memAlloc ((size_t)
	(pq->size * sizeof(pq->order[0]))) ;
	*/
	pq->ppOrder = (PQkey **)alloc->MemAlloc (alloc->pUserData,
										  (size_t)((pq->Size+1) * sizeof(pq->ppOrder[0]))) ;
	/* the previous line is a patch to compensate for the fact that IBM */
	/* machines return a null on a malloc of zero bytes (unlike SGI),   */
	/* so we have to put in this defense to guard against a memory      */
	/* fault four lines down. from fossum@austin.ibm.com.               */
	if (pq->ppOrder == NULL) return 0;

	p = pq->ppOrder;
	r = p + pq->Size - 1;
	for (piv = pq->pKeys, i = p; i <= r; ++piv, ++i)  {
		*i = piv;
	}

	/* Sort the indirect pointers in descending order,
	* using randomized Quicksort
	*/
	top->p = p; top->r = r; ++top;
	while (--top >= Stack)  {
		p = top->p;
		r = top->r;
		while (r > p + 10)  {
			seed = seed * 1539415821 + 1;
			i = p + seed % (r - p + 1);
			piv = *i;
			*i = *p;
			*p = piv;
			i = p - 1;
			j = r + 1;
			do {
				do { ++i; } while (GT (**i, *piv) );
				do { --j; } while (LT (**j, *piv) );
				Swap (i, j) ;
			} while (i < j) ;
			Swap (i, j) ; /* Undo last swap */
			if (i - p < r - j)  {
				top->p = j+1; top->r = r; ++top;
				r = i-1;
			} else {
				top->p = p; top->r = i-1; ++top;
				p = j+1;
			}
		}
		/* Insertion sort small lists */
		for (i = p+1; i <= r; ++i)  {
			piv = *i;
			for (j = i; j > p && LT (**(j-1), *piv) ; --j)  {
				*j = *(j-1);
			}
			*j = piv;
		}
	}
	pq->Max = pq->Size;
	pq->nInitialized = TRUE;
	pqHeapInit (pq->pHeap) ;  /* always succeeds */

#ifndef NDEBUG
	p = pq->ppOrder;
	r = p + pq->Size - 1;
	for (i = p; i < r; ++i)  {
		assert (LEQ (**(i+1), **i) );
	}
#endif

	return 1;
}

/* really tessPqSortInsert */
/* returns INV_HANDLE iff out of memory */ 
PQhandle pqInsert (TAlloc* alloc, TPriorityQ *pq, PQkey keyNew) 
{
	int curr;

	if (pq->nInitialized)  {
		return pqHeapInsert (alloc, pq->pHeap, keyNew) ;
	}
	curr = pq->Size;
	if (++ pq->Size >= pq->Max)  {
		if (!alloc->MemRealloc)
		{
			return INV_HANDLE;
		}
		else
		{
			PQkey *saveKey= pq->pKeys;
			// If the heap overflows, double its size.
			pq->Max <<= 1;
			pq->pKeys = (PQkey *)alloc->MemRealloc (alloc->pUserData, pq->pKeys, 
				(size_t)(pq->Max * sizeof (pq->pKeys[0]) ));
			if (pq->pKeys == NULL) { 
				pq->pKeys = saveKey;  // restore ptr to free upon return 
				return INV_HANDLE;
			}
		}
	}
	assert(curr != INV_HANDLE); 
	pq->pKeys[curr] = keyNew;

	/* Negative handles index the sorted array. */
	return -(curr+1);
}

/* really tessPqSortExtractMin */
PQkey pqExtractMin (TPriorityQ *pq) 
{
	PQkey sortMin, heapMin;

	if (pq->Size == 0)  {
		return pqHeapExtractMin (pq->pHeap) ;
	}
	sortMin = *(pq->ppOrder[pq->Size-1]);
	if (! pqHeapIsEmpty (pq->pHeap) ) {
		heapMin = pqHeapMinimum (pq->pHeap) ;
		if (LEQ (heapMin, sortMin) ) {
			return pqHeapExtractMin (pq->pHeap) ;
		}
	}
	do {
		-- pq->Size;
	} while (pq->Size > 0 && *(pq->ppOrder[pq->Size-1]) == NULL) ;
	return sortMin;
}

/* really tessPqSortMinimum */
PQkey pqMinimum (TPriorityQ *pq) 
{
	PQkey sortMin, heapMin;

	if (pq->Size == 0)  {
		return pqHeapMinimum (pq->pHeap) ;
	}
	sortMin = *(pq->ppOrder[pq->Size-1]);
	if (! pqHeapIsEmpty (pq->pHeap) ) {
		heapMin = pqHeapMinimum (pq->pHeap) ;
		if (LEQ (heapMin, sortMin) ) {
			return heapMin;
		}
	}
	return sortMin;
}

/* really tessPqSortIsEmpty */
int pqIsEmpty (TPriorityQ *pq) 
{
	return (pq->Size == 0) && pqHeapIsEmpty (pq->pHeap) ;
}

/* really tessPqSortDelete */
void pqDelete (TPriorityQ *pq, PQhandle curr) 
{
	if (curr >= 0)  {
		pqHeapDelete (pq->pHeap, curr) ;
		return;
	}
	curr = -(curr+1);
	assert (curr < pq->Max && pq->pKeys[curr] != NULL) ;

	pq->pKeys[curr] = NULL;
	while (pq->Size > 0 && *(pq->ppOrder[pq->Size-1]) == NULL)  {
		-- pq->Size;
	}
}
