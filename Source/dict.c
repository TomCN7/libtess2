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
#include "../Include/tesselator.h"
#include "bucketalloc.h"
#include "dict.h"

/* really tessDictListNewDict */
TDict *dictNewDict (TAlloc* alloc, void *frame, int (*leq)(void *frame, TDictKey key1, TDictKey key2)) 
{
	TDict *dict = (TDict *)alloc->MemAlloc (alloc->pUserData, sizeof (TDict) );
	TDictNode *head;

	if (dict == NULL) return NULL;

	head = &dict->Head;

	head->Key = NULL;
	head->pNext = head;
	head->pPrev = head;

	dict->pFrame = frame;
	dict->leq = leq;

	if (alloc->nDictNodeBucketSize < 16)
		alloc->nDictNodeBucketSize = 16;
	if (alloc->nDictNodeBucketSize > 4096)
		alloc->nDictNodeBucketSize = 4096;
	dict->pNodePool = CreateBucketAlloc (alloc, "Dict", sizeof(TDictNode), alloc->nDictNodeBucketSize) ;

	return dict;
}

/* really tessDictListDeleteDict */
void dictDeleteDict (TAlloc* alloc, TDict *dict) 
{
	DeleteBucketAlloc (dict->pNodePool) ;
	alloc->MemFree (alloc->pUserData, dict) ;
}

/* really tessDictListInsertBefore */
TDictNode *dictInsertBefore (TDict *dict, TDictNode *node, TDictKey key) 
{
	TDictNode *pNewNode;

	do {
		node = node->pPrev;
	} while (node->Key != NULL && ! (*dict->leq)(dict->pFrame, node->Key, key));

	pNewNode = (TDictNode *)BucketAlloc (dict->pNodePool) ;
	if (pNewNode == NULL) return NULL;

	pNewNode->Key = key;
	pNewNode->pNext = node->pNext;
	node->pNext->pPrev = pNewNode;
	pNewNode->pPrev = node;
	node->pNext = pNewNode;

	return pNewNode;
}

/* really tessDictListDelete */
void dictDelete (TDict *dict, TDictNode *node)  /*ARGSUSED*/
{
	node->pNext->pPrev = node->pPrev;
	node->pPrev->pNext = node->pNext;
	BucketFree (dict->pNodePool, node) ;
}

/* really tessDictListSearch */
TDictNode *dictSearch (TDict *dict, TDictKey key) 
{
	TDictNode *node = &dict->Head;

	do {
		node = node->pNext;
	} while (node->Key != NULL && ! (*dict->leq)(dict->pFrame, key, node->Key));

	return node;
}
