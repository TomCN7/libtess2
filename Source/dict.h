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

#ifndef DICT_LIST_H
#define DICT_LIST_H

typedef void *TDictKey;
typedef struct TDict TDict;
typedef struct TDictNode TDictNode;

typedef int (*LEQ)(void *pFrame, TDictKey Key1, TDictKey Key2);
TDict *dictNewDict(TAlloc* pAlloc, void *pFrame, LEQ);

void dictDeleteDict(TAlloc* pAlloc, TDict *pDict);

/* Search returns the node with the smallest key greater than or equal
* to the given key.  If there is no such key, returns a node whose
* key is NULL.  Similarly, Succ(Max(d)) has a NULL key, etc.
*/
TDictNode *dictSearch(TDict *pDict, TDictKey Key);
TDictNode *dictInsertBefore(TDict *pDict, TDictNode *pNode, TDictKey Key);
void dictDelete(TDict *pDict, TDictNode *pNode);

#define dictKey(n)      ((n)->Key)
#define dictSucc(n)     ((n)->pNext)
#define dictPred(n)     ((n)->pPrev)
#define dictMin(d)      ((d)->Head.pNext)
#define dictMax(d)      ((d)->Head.pPrev)
#define dictInsert(d,k) (dictInsertBefore((d),&(d)->Head,(k)))

/*** Private data structures ***/

struct TDictNode 
{
	TDictKey    Key;
	TDictNode*  pNext;
	TDictNode*  pPrev;
};

struct TDict 
{
	TDictNode   Head;
	void*       pFrame;
	TBucketAlloc* pNodePool;
    LEQ         leq;
};

#endif
