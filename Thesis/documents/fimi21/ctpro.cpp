/****************************************************************************
 File	    : ctpro.cpp
 Contents	: Mining complete frequent itemsets using CT-Pro algorithm 
              ** special edition for FIMI 2004 **
 Author		: Yudho Giri Sucahyo and Raj P. Gopalan 
 Website    : http://mirror.cs.curtin.edu.au/other/dsrg
 Copyright (c) 2002-2004, Dept of Computing, Curtin University of Technology
 ****************************************************************************/

/************* HEADER/LIBRARY FILES *****************/
#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>		// for malloc
#include <string.h>		// for strtok
#include <ctype.h>

/******************* CONSTANT **********************/
#define MAXENTRY      65535     // Maximum # of Item 
#define BUFFER         2048     // Buffer in memory, for reading transaction 
#define LONGSIZE		  4
#define SHORTSIZE		  2
#define ITEMSIZE		 24
#define MAXLENGTH        50

/************* ABSTRACT DATA TYPE *****************/
struct Item						// nodes in the CFP-Tree
{                               // to be filled in module constructTree
    unsigned short item,		// item id
		           sizeArr;     // size of the array
	unsigned long  * count;		// count 
	struct Item    * next,		// its sibling
				   * parent,    // its parent, needed for bottom up
				   * child,		// its child
				   * thread;    // its threads
};

struct ItemHeader				// each entry in itemTable
{                               // to be filled in module readDatabase
	unsigned short item;        // item id
	unsigned long  count;       // its count
	Item           * thread;    // thread of the item
};

class ItemStack                 // keep the stack of items
{
public:
	unsigned short top,         // top
				   size;        // size
	Item           ** arr;      // arr is a pointer to an array of Item

	// CONSTRUCTOR
	ItemStack(unsigned short s) { top=0; size=s; arr = (Item **) malloc (size*ITEMSIZE); }

	// METHOD
	void push(Item * i) { arr[top++] = i; }
	Item * pop() { return arr[--top]; }
	bool isAvail() { return (top>0)? true : false; }
	void deallocate() { free(arr); }
};

struct FreqPattern {
	unsigned short item;
	short          index;
	unsigned long  count;
	FreqPattern   *parent;		
	FreqPattern   *child;
	FreqPattern   *next;
};

class FPStack                   // keep the stack of items
{
public:
	unsigned short top,         // top
				   * level,
				   size;        // size
	FreqPattern	   ** arr;      

	// CONSTRUCTOR
	FPStack(unsigned short s) { top=0; size=s; 
								arr = (FreqPattern **) malloc (size*LONGSIZE);
								level = (unsigned short *) malloc (size * SHORTSIZE); }

	// METHOD
	void push(FreqPattern * p, unsigned short l)  { arr[top] = p; level[top] = l; top++;}
	void pop(FreqPattern ** p, unsigned short *l) { --top; *p=arr[top]; *l=level[top]; }
	bool isAvail() { return (top>0)? true : false; }
	void deallocate() { free(arr); free(level); }
};

/************* GLOBAL VARIABLE *****************/
ItemHeader		* itemTable;		 // itemTable keeps all 1-freq itemsets
Item 		   ** binItem;			 // recycle bin for deleted Items
FreqPattern		* binFP=NULL;        // recycle bin for deleted FreqPattern
unsigned short    num1FI=1,          // number of frequent items
			      * pattern;         // pattern is an array of unsigned short
unsigned long     * itemTableMap,	 // used for mapping process
				  totalFI=1,		 // total frequent itemsets generated
				  * lengthTable,   
				  ** countTable,
				  numTrans,          // number of transactions
			      absSupport;		 // support in transaction 
FILE             *fIn, *fOut;					 // pointer to input and output file


/****************************************************
 * Name:    sortItem
 * Purpose: sort items in current tid
 ****************************************************/
void sortItem(unsigned short * endTable)
{
	unsigned short *ii, valItem, *minIdx;

	for (unsigned short * startIdx=pattern+1; startIdx < endTable; startIdx++)
	{
		minIdx = startIdx;
		for (ii = startIdx+1; ii <= endTable; ii++)		
			if (*ii < *minIdx)  minIdx = ii;
		if (minIdx != startIdx)
		{
			valItem   = *startIdx;  // put the smallest item in a correct position
			*startIdx = *minIdx;  
			*minIdx   = valItem;
		}
	}
} 

/****************************************************
 * Name:    sortItemTable
 * Purpose: sort the item table based on item's freq
 ****************************************************/
void sortItemTable()
{
	struct ItemHeader * pStart, * pEnd = itemTable+num1FI-1, * pSelect;
	unsigned int temp;

	for (itemTable++; itemTable < pEnd; itemTable++)
	{
		pSelect = itemTable;
		for (pStart=itemTable+1; pStart <= pEnd; pStart++)
			if (pStart->count > pSelect->count) pSelect = pStart;
		if (pSelect != itemTable)
		{
			temp             = itemTable->item;
			itemTable->item  = pSelect->item;
			pSelect->item    = temp;
			temp             = pSelect->count;
			pSelect->count   = itemTable->count;
			itemTable->count = temp;
		}
	}
	itemTable-=num1FI-1;
} 

/*************************************************************
 * Name:    newItem
 * Purpose: create a new Item
 *************************************************************/
inline Item * newItem(unsigned short idx)
{
	Item * i;
	if (i=binItem[idx])
		binItem[idx] = binItem[idx]->next;
	else
	{
		i=(Item *) malloc (ITEMSIZE);
		i->count = (unsigned long *) malloc ((i->sizeArr = idx) * LONGSIZE);
	}
	memset(i->count, 0, idx * LONGSIZE);
	return i;
}

/*************************************************************
 * Name:    deleteItem
 * Purpose: delete an item in the array of Item
 *************************************************************/
inline void deleteItem(Item * i, unsigned short index)
{
	if (i->sizeArr < index)
	{	
		i->next = binItem[i->sizeArr];
		binItem[i->sizeArr] = i;
	}
	else
	{
		free(i->count);
		free(i);
	}
}

/*************************************************************
 * Name:    cleanItem
 * Purpose: clean the item array
 *************************************************************/
inline void cleanItem(Item ** pIPar, Item * pI, unsigned short i)
{
	Item *c = pI, *s, *p;
	while(c) 
	{
		if(c->child) break;
		else 
		{
			s = c->next;
			p = c->parent;
			deleteItem(c, i);	
			if(p) p->child = s;
			else  *pIPar = s;
			c = p;
		}
	}
}

/*************************************************************
 * Name:    releaseItem
 *************************************************************/
void releaseItem(Item * pHI, unsigned short i)
{
	if (!pHI) return;
	ItemStack itemStack(num1FI);
	Item * pI=NULL;
	itemStack.push(pHI);
	while (itemStack.isAvail())
	{
		pI=itemStack.pop();
		if (pI->next) itemStack.push(pI->next);
		if (pI->child) itemStack.push(pI->child);
		else  cleanItem(&pHI, pI, i);
	}
}

/*************************************************************
 * Name:    newFP
 * Purpose: create a new FreqPattern
 *************************************************************/
inline FreqPattern * newFP()
{
	FreqPattern * p;
	if (binFP)
	{
		p = binFP;
		binFP = binFP->next;
	}
	else
		p = (FreqPattern *) malloc (sizeof (FreqPattern));
	return p;
}

/*************************************************************
 * Name:    deleteFP
 *************************************************************/
inline void deleteFP(FreqPattern * p)
{
	p->next = binFP;
	binFP = p;
}

/*************************************************************
 * Name:    appendFP
 *************************************************************/
inline void appendFP(ItemHeader *itemTable, FreqPattern* pPar, unsigned short loc)
{
	FreqPattern * p;
	p = newFP();
	p->item = itemTable[loc].item;
	p->index = loc;
	p->child = NULL;
	p->parent = pPar;
	p->count = itemTable[loc].count;
	p->next = pPar->child;
	pPar->child = p;
}

/*************************************************************
 * Name:    printFP
 *************************************************************/
void printFP(FreqPattern * currFP)
{
	FPStack tempStack(num1FI);
	FreqPattern *v;
	unsigned short n, lev=1, ii; 

	tempStack.push(currFP, lev);
	while(tempStack.isAvail()) {
		tempStack.pop(&v, &n);
		pattern[n-1] = v->item;
		for (ii=0; ii<n; ii++)
			fprintf(fOut, "%u ", pattern[ii]);
		fprintf(fOut, "(%u)\n", v->count);
		lengthTable[ii-1]++;
		totalFI++;

		if(v->next) 
			tempStack.push(v->next, n);
		if(v->child) 
			tempStack.push(v->child, n+1);
	}
	tempStack.deallocate(); 
} 

/*************************************************************
 * Name:    changeIdxFP
 *************************************************************/
void changeIdxFP(ItemHeader * itemTable, FreqPattern * currProj)
{
	// replace OLD LocalIdx by NEW LocalIdx
	FPStack tempStack(num1FI);
	FreqPattern *v;
	unsigned short n;
	if(currProj->child) tempStack.push(currProj->child, 0);
	while(tempStack.isAvail()) {
		tempStack.pop(&v, &n);
		if(itemTable[v->index].count >= absSupport) 		
	 		 v->index = itemTable[v->index].item;	
		else v->index = 0;
		if(v->next) tempStack.push(v->next, 0);
		if(v->child) tempStack.push(v->child, 0);
	}
}

/*******************************************************************************
 * Name:    parse_args
 * Purpose: parse and check arguments
 * Imports: argc, argv
 ******************************************************************************/
void parse_args(int argc, char** argv)
{
	if (argc != 4) 
	{   
		printf("Usage: fim_all <input-filename> <absolute-support> <output-filename>\n");
	    exit(0);
	}
	if (!(fIn = fopen(argv[1], "r")))
	{
		printf("Error in input file\n");
		exit(0);
	}
	if (!(fOut = fopen(argv[3], "w")))
	{
		printf("Error in output file\n");
		exit(0);
	}
	absSupport = atoi(argv[2]);
	if (absSupport < 0)			// will not be executed as now we declare absSupport as unsigned
	{
		printf("Invalid support value\n");
		exit(0);
	}
}

/*************************************************************
 * Name:    readDatabase
 * Purpose: read the database to get the frequent items
 *************************************************************/
void readDatabase()
{
	char string[BUFFER];                 // each line read from the database
	char * token;
	unsigned short item;							 // item in the transaction
	unsigned long  tmp;                  // just a counter

	//----- read each transaction, increment the count in itemTableMap
	itemTableMap  = (unsigned long *) calloc (MAXENTRY, LONGSIZE);      // array of unsigned int
	for (tmp=1; fgets(string, BUFFER, fIn); tmp++)   // read each transaction
	{
		token=strtok(string," \t\n");    // read each item in the transaction
		while (token!=NULL)
		{
			if (isdigit(*token))
				itemTableMap[atoi(token)]++;
			token=strtok(NULL, " \t\n");
		}
	} 
	tmp--;
	numTrans = tmp;
    absSupport--;

    //----- check frequent items in itemTableMap
	for (item=0, tmp=0; item < MAXENTRY; item++, itemTableMap++)	
		if (*itemTableMap > absSupport) num1FI++;
	itemTableMap-= item;	// set the pointer to the head position

	//----- move all frequent items to itemTable
	itemTable = (struct ItemHeader *) malloc (num1FI * sizeof (struct ItemHeader));
	for (tmp=1, item=0, itemTable++; tmp<num1FI; item++)
		if (itemTableMap[item] > absSupport)
		{
			itemTable->item = item;
			itemTable->count = itemTableMap[item];
			itemTable++;
			tmp++;
		}
	itemTable-=num1FI;							// put it back to the head position
	sortItemTable();							// sort itemTable based on frequency
}

/*************************************************************
 * Name:    getPattern
 *************************************************************/
unsigned short getPattern(Item * pI, unsigned short idx, unsigned short * pat)
{
	unsigned short ii=1;
	
	while (pI)
	{
		pat[ii++] = pI->item;
		if (idx < pI->item-1) pI=pI->parent;
		else pI=NULL;
	}
	ii--;
	return ii;
}

/*************************************************************
 * Name:    insertToTree
 * Purpose: insert the sorted tid into tree
 * Imports: number of items in the tid, the items array
 *************************************************************/
void insertToTree(unsigned short numItem, unsigned short *itemNo, Item * pTR1)
{
	unsigned short item, pos=*itemNo-1;
	Item * pTR2, * pTR3;
	
	for (item=2, itemNo++; item < numItem; item++, itemNo++, pTR1=pTR2)	// for the rest of items in tid
		if (pTR3=pTR2=pTR1->child)				// has child?
		{
			if (pTR3->item > *itemNo)
			{
				pTR1->child = pTR2 = newItem(pTR1->sizeArr);
				pTR2->item = *itemNo;
				pTR2->child = NULL;
				pTR2->parent = pTR1;
				pTR2->next = pTR3;
				pTR2->thread = itemTable[*itemNo].thread;
				itemTable[*itemNo].thread = pTR2;
			}
			else
			{
				for (; pTR2 && (pTR2->item < *itemNo); pTR2=pTR2->next)
						pTR3=pTR2;				 	 // get the right place
				if (!pTR2 || (pTR2->item!=*itemNo))  // if not found, create a new node
				{                
					pTR2 = newItem(pTR1->sizeArr);
					pTR2->item   = *itemNo;
					pTR2->child  = NULL;
					pTR2->next   = pTR3->next;
					pTR3->next   = pTR2;
					pTR2->parent = pTR1;   //-- previous tree version has no parent 
					pTR2->thread = itemTable[*itemNo].thread;
					itemTable[*itemNo].thread = pTR2;
				}
			}
		}	
		else    // no child? just create a new one
		{
			pTR1->child  = pTR2 = newItem(pTR1->sizeArr);
			pTR2->item   = *itemNo;
			pTR2->next   = pTR2->child = NULL;
			pTR2->parent = pTR1;
			pTR2->thread = itemTable[*itemNo].thread;
			itemTable[*itemNo].thread = pTR2;
		}
	pTR1->count[pos]++;  
}

void insertToTree(ItemHeader * itemTable, unsigned short numItem, unsigned short *itemNo, Item * pTR1, unsigned long c)
{
	unsigned short item, pos=*itemNo-1;
	Item * pTR2, * pTR3;
	pTR1->count[pos] += c;  
	for (item=2, itemNo++; item < numItem; item++, itemNo++, pTR1=pTR2, pTR2->count[pos]+=c)	// for the rest of items in tid
		if (pTR3=pTR2=pTR1->child)				// has child?
		{
			if (pTR3->item > *itemNo)
			{
				pTR1->child = pTR2 = newItem(pTR1->sizeArr);
				pTR2->item = *itemNo;
				pTR2->child = NULL;
				pTR2->parent = pTR1;
				pTR2->next = pTR3;
				pTR2->thread = itemTable[*itemNo].thread;
				itemTable[*itemNo].thread = pTR2;
			}
			else
			{
				for (; pTR2 && (pTR2->item < *itemNo); pTR2=pTR2->next)
					pTR3=pTR2;				 	      // get the right place
				if (!pTR2 || (pTR2->item!=*itemNo))   // if not found, create a new node
				{                
					pTR2 = newItem(pTR1->sizeArr);
					pTR2->item   = *itemNo;
					pTR2->child  = NULL;
					pTR2->next   = pTR3->next;
					pTR3->next   = pTR2;
					pTR2->parent = pTR1;   //-- previous tree version has 
					pTR2->thread = itemTable[*itemNo].thread;
					itemTable[*itemNo].thread = pTR2;
				}
			}
		}	
		else    // no child? just create a new one
		{
			pTR1->child = pTR2 = newItem(pTR1->sizeArr);
			pTR2->item = *itemNo;
			pTR2->next = pTR2->child = NULL;
			pTR2->parent = pTR1;
			pTR2->thread = itemTable[*itemNo].thread;
			itemTable[*itemNo].thread = pTR2;
		}
}

/******************************************************************************
 * Name   : buildBaseTree
 * Purpose: construct the leftmost branch of the tree
 ******************************************************************************/
void buildBaseTree(Item ** itemTable2)
{
	Item * pTR;
	unsigned short item;

	itemTable++;
	pTR = itemTable->thread = itemTable2[1] = newItem(1);
	pTR->item   = 1;
	pTR->parent = pTR->next = pTR->thread = NULL;

	//--- construct the leftmost branch
	for (item=2, itemTable++; item < num1FI; item++, itemTable++)		     
	{
		pTR->child = itemTable->thread = itemTable2[item] = newItem(item);
		pTR->child->parent = pTR;
		pTR = pTR->child;
		pTR->item = item;
		pTR->next = pTR->thread = NULL;
	}
	itemTable -= num1FI;
	pTR->child = NULL;
}

/*******************************************************************************
 * Name:    constructTree
 * Purpose: reread only 1-freq items from DB and construct the CFP-Tree
 ******************************************************************************/
void constructTree()
{
	char string[BUFFER];		// each line read from the database
	char * token;
	unsigned short item;		
	unsigned long  ii;
	Item ** itemTable2;

	//--- construct the left most branch
	itemTable2 = (Item **) calloc (num1FI, sizeof (Item *));
	buildBaseTree(itemTable2);
	countTable = (unsigned long **) calloc (num1FI, LONGSIZE);
	memset(itemTableMap, 0, MAXENTRY*LONGSIZE);

	for (item=1;  item < num1FI; item++)		     
	{
		itemTableMap[itemTable[item].item] = item;
		countTable[item] = (unsigned long *) calloc (num1FI, LONGSIZE);
	}

	pattern = (unsigned short *) malloc (num1FI * SHORTSIZE);
	rewind(fIn);							// rewind the input file
	while (fgets(string, BUFFER, fIn))		// reread each transaction
	{
		token=strtok(string," \n\t");	    // read every item in the transaction
		item=1;
		while (token)
		{
			if (isdigit(*token))
			{
				ii=atoi(token);
				if (itemTableMap[ii])
					pattern[item++] = (unsigned short) itemTableMap[ii];
			}
			token=strtok(NULL, " \n\t");
		}
		if (item>1)
		{
			sortItem(pattern+item-1);			// sort the temporary array
			insertToTree(item, pattern+1, itemTable2[pattern[1]]);
		}
	} 
	fclose(fIn);			   // close the input file
	free(itemTableMap);
	free(itemTable2);
}

/*******************************************************************************
 * Name:    miningLocal
 * Purpose: mine the local tree
 ******************************************************************************/
void miningLocal(Item * headItem, ItemHeader * itemTable, unsigned short loc, FreqPattern * currFP, unsigned short lev)
{
	unsigned short ii, jj, locM;
	unsigned long  sum, sum2;
	FreqPattern * nowFP;
	FPStack stackFP(num1FI);
	Item * pIS, * pISPar;

	for (ii=loc-1; ii; ii--) appendFP(itemTable, currFP, ii);		
	if(currFP->child->next) stackFP.push(currFP->child->next, lev+1);

	while(stackFP.isAvail()) 
	{
		stackFP.pop(&nowFP, &lev);
		if(nowFP->next) stackFP.push(nowFP->next, lev);
		if(!nowFP->index) continue;

		for(ii=1; ii<nowFP->index; ii++) {
			itemTable[ii].count = 0;
			for (pIS=itemTable[ii].thread; pIS; pIS=pIS->thread)
				for (jj=0; jj<pIS->sizeArr; jj++)
					pIS->count[jj] = 0;
			itemTable[ii].thread = NULL;
		}

		if (nowFP->index > 1)
			for (pIS=itemTable[nowFP->index].thread; pIS; pIS=pIS->thread)
				for (pISPar=pIS->parent; pISPar;)
				{
					for (sum=sum2=jj=0; jj<pISPar->sizeArr; jj++)
					{
						sum += pISPar->count[jj];
						sum2 += pIS->count[jj];
					}

					if (sum2)
					{
						if (!sum)
						{
							pISPar->thread = itemTable[pISPar->item].thread;
							itemTable[pISPar->item].thread = pISPar;
						}
						for (jj=0; jj<pISPar->sizeArr; jj++)
							pISPar->count[jj] += pIS->count[jj];

						itemTable[pISPar->item].count += sum2;
						pISPar=pISPar->parent;
					}
					else  
						pISPar=NULL;
				}

		for (ii=locM=1; ii<nowFP->index; ii++)
			if (itemTable[ii].count > absSupport) pattern[locM++] = ii;
		if (locM > 1)
		{
			if (lev > 1) 
			{
				for (ii=locM-1; ii; ii--) appendFP(itemTable, nowFP, pattern[ii]);		
				if (nowFP->child->next)
					stackFP.push(nowFP->child->next, lev+1);
			}
			else
				stackFP.push(nowFP->child, lev+1);
		}
	}
	free(itemTable);
	releaseItem(headItem, currFP->index);	
	stackFP.deallocate(); 
}

/*******************************************************************************
 * Name:    updateCountTable
 ******************************************************************************/
void updateCountTable()
{
	unsigned short ii, jj, kk, * pat, idx, sArr;
	ItemStack itemStack(num1FI);
	Item * currI, * childI;

	pat = (unsigned short *) malloc (num1FI * SHORTSIZE);
	itemStack.push(itemTable[1].thread);
	while (itemStack.isAvail())
		for (currI = itemStack.pop(); currI; currI=childI)
		{
			childI = currI->child;
			sArr=(currI->sizeArr == currI->item)? currI->sizeArr-1 : currI->sizeArr;
			for (ii=0; ii<sArr; ii++)
				if (currI->count[ii])
				{
					idx = getPattern(currI, ii, pat);
					for (jj=idx-1; jj; jj--)
						for (kk=idx; kk>jj; kk--)
							countTable[pat[jj]][pat[kk]]+=currI->count[ii];
				}
			if (currI->next) itemStack.push(currI->next);
		}
	free(pat);
	itemStack.deallocate(); 
}

/*******************************************************************************
 * Name:    copyTree
 ******************************************************************************/
void copyTree(unsigned short pos, ItemHeader * itemTable2, Item * itemTable3)
{
	unsigned short ii, jj, kk, * pat, idx, sArr;
	Item * currI, *tmpCurr;

	pat = (unsigned short *) malloc (num1FI * SHORTSIZE);
	for (currI=itemTable[pos].thread; currI; currI=tmpCurr)
	{
		sArr=(currI->sizeArr == currI->item)? currI->sizeArr-1 : currI->sizeArr;
		for (ii=0; ii<sArr; ii++)
			if (currI->count[ii])
			{
				idx = getPattern(currI, ii, pat);
				for (kk=1, jj=idx; jj>1; jj--)
					if (countTable[pos][pat[jj]] > absSupport)
						pattern[kk++] = itemTable[pat[jj]].item;
				if (kk>1)
					insertToTree(itemTable2, kk, pattern+1, itemTable3[pattern[1]].thread, currI->count[ii]);
				currI->parent->count[ii] += currI->count[ii];
			}
		tmpCurr = currI->thread;
		free(currI);
	}
	free(pat);
}

/*******************************************************************************
 * Name:    removeLast
 ******************************************************************************/
void removeLast(unsigned short pos)
{
	unsigned short ii, sArr;
	Item * currI, *tmpCurr;

	for (currI=itemTable[pos].thread; currI; currI=tmpCurr)
	{
		sArr=(currI->sizeArr == currI->item)? currI->sizeArr-1 : currI->sizeArr;
		for (ii=0; ii<sArr; ii++)
			if (currI->count[ii])
				currI->parent->count[ii] += currI->count[ii];
		tmpCurr = currI->thread;
		free(currI);
	}
}

/*******************************************************************************
 * Name   : MineFI
 * Purpose: to mine the frequent itemsets
 ******************************************************************************/
void MineFI()
{
	unsigned short ii, jj, item, num1FILocal, numFP;
	FreqPattern * currFP;
	Item * pI, * itemTable3;
	ItemHeader * itemTable2;

	updateCountTable();

	itemTableMap = (unsigned long *) malloc (num1FI * LONGSIZE);
	itemTable3   = (Item *) malloc (num1FI * ITEMSIZE);

	for (numFP=num1FI-1; numFP; numFP--)
	{
		currFP = (FreqPattern *) malloc (sizeof (FreqPattern));
		currFP->item  = itemTable[numFP].item;
		currFP->index = numFP;
		currFP->count = itemTable[numFP].count;
		currFP->next  = currFP->parent = currFP->child = NULL;

		item = currFP->index;

		for (ii=num1FILocal=1; ii<item; ii++) 
			if (countTable[item][ii] > absSupport)
				itemTableMap[num1FILocal++] = ii;

		if (num1FILocal > 2)
		{
			itemTable2 = (ItemHeader *) malloc (num1FILocal * sizeof (ItemHeader));
			itemTable2[1].item   = itemTable[itemTableMap[1]].item;
			itemTable2[1].count  = countTable[item][itemTableMap[1]];
			itemTable2[1].thread = itemTable3[1].thread = pI = newItem(1);
			itemTable[itemTableMap[1]].item = 1;
			pI->item = 1;
			pI->next = pI->parent = pI->thread = NULL;
			for (ii=2; ii < num1FILocal; ii++)
			{
				itemTable2[ii].item   = itemTable[itemTableMap[ii]].item;
				itemTable2[ii].count  = countTable[item][itemTableMap[ii]];
				itemTable2[ii].thread = itemTable3[ii].thread = pI->child = newItem(ii);
				itemTable[itemTableMap[ii]].item = ii;
				pI->child->parent = pI;
				pI = pI->child;
				pI->item = ii;
				pI->next = pI->thread = NULL; 
			}
			pI->child = NULL;

			changeIdxFP(itemTable, currFP);
			
			copyTree(item, itemTable2, itemTable3);

			itemTable[itemTableMap[1]].item = itemTable2[1].item;
			pI= itemTable2[1].thread; 
			for (ii=2, pI=pI->child; ii<num1FILocal; ii++, pI=pI->child)
			{
				itemTable[itemTableMap[ii]].item = itemTable2[ii].item;
				for (jj=0; (jj<pI->sizeArr-1) && !pI->count[jj]; jj++);
				if (jj==pI->sizeArr-1) 
					pI->parent = NULL;
			}

			miningLocal(itemTable2[1].thread, itemTable2, num1FILocal, currFP, 1);
		}
		else 
		{
			if (num1FILocal==2)
			{
				currFP->child         = newFP();
				currFP->child->parent = currFP;
				currFP->child->item   = itemTable[itemTableMap[1]].item;
				currFP->child->index  = -1;
				currFP->child->count  = countTable[item][itemTableMap[1]];
				currFP->child->next   = currFP->child->child = NULL;
			}
			removeLast(item);
		}

		printFP(currFP);
	}
	fprintf(fOut, "(%u)\n", numTrans);    // the empty set
}

/********** MAIN FUNCTION *************/
int main(int argc, char** argv)
{   
	unsigned long ii = 0;
	parse_args(argc, argv); // check arguments

	readDatabase();			//** Step 1: identify frequent items
	lengthTable = (unsigned long *) calloc (MAXLENGTH, LONGSIZE);

	if (num1FI>1)			// if we got any 1-freq items, do next steps
	{
		binItem = (Item **) calloc (num1FI, ITEMSIZE);	
		constructTree();	//** Step 2: construct the CFP-Tree
		MineFI();			//** Step 3: Mining 
	}
	printf("%u\n", totalFI);   // report the totalFI generated
	printf("1\n");			   // the empty set
	while (lengthTable[ii] && (ii<MAXLENGTH))
		printf("%u\n", lengthTable[ii++]);
	fclose(fOut);	           // close the output file
	return 0;                  // exit
}			
