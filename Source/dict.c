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
TDict *dictNewDict(TAlloc* pAlloc, void *pFrame, LEQ leq) 
{
	TDict *pDict = (TDict *)pAlloc->MemAlloc(pAlloc->pUserData, sizeof(TDict));
	TDictNode *pHead = NULL;

	if (pDict == NULL) return NULL;

	pHead = &pDict->Head;

	pHead->Key = NULL;
	pHead->pNext = pHead;
	pHead->pPrev = pHead;

	pDict->pFrame = pFrame;
	pDict->leq = leq;

	if (pAlloc->nDictNodeBucketSize < 16)
		pAlloc->nDictNodeBucketSize = 16;
	if (pAlloc->nDictNodeBucketSize > 4096)
		pAlloc->nDictNodeBucketSize = 4096;

    pDict->pNodePool = CreateBucketAlloc(pAlloc, "Dict", sizeof(TDictNode), pAlloc->nDictNodeBucketSize);

	return pDict;
}

/* really tessDictListDeleteDict */
void dictDeleteDict(TAlloc* pAlloc, TDict *pDict) 
{
	DeleteBucketAlloc(pDict->pNodePool);
	pAlloc->MemFree(pAlloc->pUserData, pDict);
}

/* really tessDictListInsertBefore */
TDictNode *dictInsertBefore(TDict *pDict, TDictNode *pNode, TDictKey Key) 
{
	TDictNode *pNewNode = NULL;

	do 
    {
		pNode = pNode->pPrev;
	} while (pNode->Key != NULL && !(*pDict->leq)(pDict->pFrame, pNode->Key, Key));

	pNewNode = (TDictNode *)BucketAlloc(pDict->pNodePool);
	if (pNewNode == NULL) return NULL;

	pNewNode->Key = Key;
	pNewNode->pNext = pNode->pNext;
	pNode->pNext->pPrev = pNewNode;
	pNewNode->pPrev = pNode;
	pNode->pNext = pNewNode;

	return pNewNode;
}

/* really tessDictListDelete */
void dictDelete(TDict *pDict, TDictNode *pNode)  /*ARGSUSED*/
{
	pNode->pNext->pPrev = pNode->pPrev;
	pNode->pPrev->pNext = pNode->pNext;
	BucketFree(pDict->pNodePool, pNode);
}

/* really tessDictListSearch */
TDictNode *dictSearch(TDict *pDict, TDictKey Key) 
{
	TDictNode *pNode = &pDict->Head;

	do 
    {
		pNode = pNode->pNext;
	} while (pNode->Key != NULL && !(*pDict->leq)(pDict->pFrame, Key, pNode->Key));

	return pNode;
}
