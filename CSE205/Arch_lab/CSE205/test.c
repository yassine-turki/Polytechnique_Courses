/*
 * 
 * OVERVIEW:

 Our malloc implements a single extended list to store all the free blocks. In the beginning we
 initiate the heap with mm_init, creating a prologue block and epilogue footer for alignments purposes.
 We have a global variable called heap_listp that points to the "payload"(technically 0) of the prologue block.
 This is what we will use to point to the blocks in the heap.

 When malloc is called, do a first-fit search of our global_list (aka the extended list) to find
 a place that will fit. Once the proper block is found, the block becomes allocated. BUT, if the free block
 size minus the size we are asking for is big enough to hold another block, we split that block and add it
 to our free list. Otherwise, we give the entire free block to the requested malloc.

 Upon freeing, we simply free the block, but the most important thing here is the coalescing issue. In our
 coalesce method we do checks to the previous and next block of the current pointer, and then coalesce the
 necessary blocks.

 We also wrote a heap checker to test the heap's consistency. It simply runs tests to make sure the the pointers
 in the heap point to valid heap addresses, the free list contains free blocks, etc. 
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "douglaschau+leonlee",
    /* First member's full name */
    "Douglas Chau",
    /* First member's email address */
    "dchau3@binghamton.edu",
    /* Second member's full name (leave blank if none) */
    "Leon Lee",
    /* Second member's email address (leave blank if none) */
    "llee21@binghamton.edu"
};

#define WSIZE       4       /* Word and HEAD/FOOT size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define DDSIZE      16      /* Minimum size of a block */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 


/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))  
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* read size and allocation bit */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    
/* Used for valid heap checking */
#define GET_ALIGN(p) (GET(p) & 0x7)

/* Calculation for header and footer of a block */
#define HEAD(bp)       ((char *)(bp) - WSIZE)                      
#define FOOT(bp)       ((char *)(bp) + GET_SIZE(HEAD(bp)) - DSIZE) 

/* Calculations for the next and previous blocks based on size */
#define NEXT(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
char *list_head = 0; //list of free blocks
char *epilogue_block = 0; /* Pointer to epilogue block */
int free_count = 0; //# of free blocks  


static char *heap_listp = 0;  /* Pointer to first block */
char *free_list_head_ptr = 0; //list of free blocks
char *epilogue_block_ptr = 0; /* Pointer to epilogue block */
int num_free_blocks = 0; // Counter for number of free blocks


/* Prototypes for helper methods */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add(void *bp);
static void remove_block(void *bp);
static int mm_checkheap(void);
static int checkFreeInList(void);
static int checkOverlap(void);
static int checkCoalesceAndFree(void);
static int mm_valid_heap(void);

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue HEAD */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue FOOT */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue HEAD */
    epilogue_block = (heap_listp + (3*WSIZE)); //for checkheap
    heap_listp += (2*WSIZE);                     
    list_head = 0; //initialize global list to indicate empty
    free_count = 0; //no free blocks
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL) 
        return -1;
    return 0;
}
/*
* extend_heap - increases the heap by adding a free block at the end of size size bytes
*/
static void *extend_heap(size_t size){
    char *bp;
    size_t asize; //makes sure the block will be aligned
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1))/ DSIZE);
    if ((long)(bp = mem_sbrk(asize)) == -1)    
        return NULL;
    //initialize free block HEAD and epilogue HEAD
    PUT(HEAD(bp), PACK(asize, 0)); //sets HEAD as free
    PUT(FOOT(bp), PACK(asize, 0)); //sets FOOT as free
    PUT(HEAD(NEXT(bp)), PACK(0,1)); //new epilogue HEAD

    return coalesce(bp); //coalesce if possible
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) 
{
    size_t asize;
    size_t extendsize;
    char *bp;
    
    if (size <= 0) //ignore if size is 0
        return NULL;    

    if (size<=DSIZE) //if size is less than minimum block, set to min
        asize = DDSIZE;
    else //align the size to 8
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1))/ DSIZE);
    if ((bp = find_fit(asize)) != NULL){ //if there is a fit, place it and return
        place(bp, asize);
        return bp;
    }
    if (asize > CHUNKSIZE) //else there is no fit, extend the heap by the bigger of either asize or chunksize
        extendsize = asize;
    else extendsize = CHUNKSIZE;
    if ((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

} 
/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize){
    if (free_count == 0)
        return NULL;
    void *bp = list_head; //point to the beginning of free list
    int i;
    for (i = 0; i < free_count; i++){ //iterate through the list for a free block
        if (asize <= GET_SIZE(HEAD(bp)))
            return bp;
        bp = (char *) GET(bp+WSIZE); //go to the next free block
    }
    return NULL;
}
/* 
 * place - Place a block of asize and split if the remainder of block is at least 16 
 */
static void place(void *bp, size_t asize){
    void *next;
    size_t currentSize = GET_SIZE(HEAD(bp)); //size of current block
    size_t sizeDiff = currentSize - asize; /* Difference of size to check if we can split the block*/
    if (sizeDiff >= DDSIZE) {
        remove_block(bp); //remove the block from free list
        PUT(HEAD(bp), PACK(asize, 1)); //pack exact size needed
        PUT(FOOT(bp), PACK(asize, 1));
        next = NEXT(bp); //get pointer to new smaller block
        PUT(HEAD(next), PACK(sizeDiff, 0));
        PUT(FOOT(next), PACK(sizeDiff, 0));
        add(next); //add new block to the list
    }
    else{ /* If block isn't large enough to split, use all space */
        PUT(HEAD(bp), PACK(currentSize,1));
        PUT(FOOT(bp), PACK(currentSize,1));
        remove_block(bp); //remove the block from free list
    }
}

/*
* remove_block- removes the block from the free list and fixes pointers
*/
static void remove_block(void *bp){
    free_count--;
    if (GET(bp) == 0 && GET(bp+WSIZE) == 0){ //if no next pointer and no prev pointer means it is the only free block
        list_head = 0;
    } 
    else if (GET(bp) == 0 && GET(bp + WSIZE) != 0){ //else if next exists but prev doesnt. indicates first of list
        list_head = (char *)GET(bp+WSIZE);
        PUT((char *)GET(bp + WSIZE), 0); //set next block's prev to 0
    } 
    else if (GET(bp) != 0 && GET(bp + WSIZE) == 0){ //else if prev exists but next doesnt. means it is end of list
        PUT(((char *)GET(bp) + WSIZE), 0); //set the prev block's next to 0
    }
    else{ //else item somewhere in middle of list
        PUT(((char *)GET(bp) + WSIZE), GET(bp + WSIZE));   //set prev block's next to point to bp's next
        PUT(((char *)GET(bp + WSIZE)), GET(bp)); //set next's prev to prev
    }
}
/*
* add - sets the new free block to the first of the list
*/
static void add(void *bp){
    free_count++;
    if ((free_count-1) == 0){ //if list is empty
        list_head = bp;
        PUT(bp, 0);  //sets previous and next to 0
        PUT(bp+WSIZE, 0);
        return;
    }
    PUT(((char *)list_head), (int)bp); //set the current head of the list's previous to bp
    PUT(bp, 0); //sets bp's previous to 0
    PUT(bp + WSIZE, (int)list_head); //sets bp's next to the head of the list
    list_head = bp;  //sets the head of the list to bp
}
/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    //if freeing nothing or if heap isnt initialized yet, return
    if(bp == 0 || heap_listp == 0) 
        return;

    size_t size = GET_SIZE(HEAD(bp)); //get size of the block

    //set alloc bit and size
    PUT(HEAD(bp), PACK(size, 0));
    PUT(FOOT(bp), PACK(size, 0));

    coalesce(bp);
}

/*
 * coalesce - coalesce if possible, returns original bp or new coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(HEAD(PREV(bp)));
    size_t next_alloc = GET_ALLOC(HEAD(NEXT(bp)));
    size_t size = GET_SIZE(HEAD(bp));
    
    if (prev_alloc && next_alloc) {            // if next and prev are allocated
        add(bp);
        return bp;
    }
    
    else if (prev_alloc && !next_alloc) {      //if next is free but previous is allocated
        remove_block(NEXT(bp)); //remove block from free list
        size += GET_SIZE(HEAD(NEXT(bp))); //add total size of coalesced block
        PUT(HEAD(bp), PACK(size, 0)); //reflect changes in header and footer
        PUT(FOOT(bp), PACK(size,0));
        add(bp); //add block to the list
    }
    
    else if (!prev_alloc && next_alloc) {      // if prev is free but next is allocated
        remove_block(PREV(bp));
        size += GET_SIZE(HEAD(PREV(bp)));
        PUT(HEAD(PREV(bp)), PACK(size, 0));
        PUT(FOOT(bp), PACK(size, 0));
        bp = PREV(bp); //point bp to the previous block
        add(bp); //add to the list
    }

    else {      //if both next and prev are free
        remove_block(PREV(bp)); //remove previous and next block
        remove_block(NEXT(bp));
        size += GET_SIZE(HEAD(PREV(bp))) + GET_SIZE(FOOT(NEXT(bp))); //add total size of blocks
        PUT(HEAD(PREV(bp)), PACK(size, 0));
        PUT(FOOT(NEXT(bp)), PACK(size, 0));
        bp = PREV(bp);
        add(bp);
    }
        //mm_checkheap();

    return bp;
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    void *temp;
    size_t tempsize;
    size_t copySize;
    size_t previous_alloc = GET_ALLOC(HEAD(PREV(oldptr))); //get allocation status of prev and next blocks
    size_t next_alloc = GET_ALLOC(HEAD(NEXT(oldptr)));
    size_t currentSize = GET_SIZE(HEAD(oldptr)); //size of current block
    int incSize;
    
    if (oldptr == NULL)  //if pointer is null, then it is the same as malloc
        return mm_malloc(size);

    if (size == 0){ //if size is 0, it is the same as freeing
        mm_free(ptr);
        return NULL;
    }

    if(currentSize  < size + DSIZE) // check if we need to increase size
        incSize = 1;
    else
        incSize = 0;

    // if shrinking the block will give enough room for a free block
    if(incSize == 0 && (currentSize - size - DSIZE) > DDSIZE){ 
        if (size <= DSIZE)
            size = DDSIZE;
        else
            size=DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // align

        if((currentSize - size) > DDSIZE){ //if there is still room for a new block after adjusting
            PUT(HEAD(oldptr), PACK(size, 1));  //set header and footer to reflect smaller size
            PUT(FOOT(oldptr), PACK(size, 1)); 
        
            newptr = oldptr;
            oldptr =  (NEXT(newptr)); // reset point to new block
            int packSize = currentSize - size;
            PUT(HEAD(oldptr), PACK(packSize, 0)); //set allocation bit and size
            PUT(FOOT(oldptr), PACK(packSize, 0));
            coalesce(oldptr);

            return newptr;
        }
    }
    
    //if new space too small to be a free block, return; nothing needs to be done
    if(incSize == 0) {
        return ptr;
    }
    else {
            int prevsize = GET_SIZE(HEAD(PREV(oldptr))); //size of previous block
            int nextsize = GET_SIZE(HEAD(NEXT(oldptr))); //size of next block
            if (next_alloc == 0 && previous_alloc == 0 && (prevsize + nextsize + currentSize) >= (size + DSIZE)){ //if next and prev are free and combining is enough to satisfy the new size
                newptr = PREV(oldptr); //the new address of the expanded block

                temp = NEXT(oldptr); //address of next block

                //temp size is size of next and prev blocks -- ie the added size to the current block.
                tempsize = prevsize + nextsize;

                remove_block(PREV(oldptr)); //we'll be using these blocks
                remove_block(NEXT(oldptr));

                if (size <= DSIZE) //adjust
                    size = DDSIZE;
                else
                    size =  DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 
        
                // take all space if block can't be split
                if((tempsize + currentSize) < (size + 2*DSIZE))
                    size = tempsize + currentSize;
                 
                PUT(HEAD(newptr), PACK(size, 1)); //reflect new size
    
                copySize = GET_SIZE(HEAD(oldptr)); //calculate size to copy
                memcpy(newptr, oldptr, copySize);
                
                PUT(FOOT(newptr), PACK(size, 1)); //has to go after copy or else it will get overwritten
                                
                if((tempsize + currentSize) >= (size + DDSIZE)){ 
                    temp = NEXT(newptr); //the new empty block
                    int newsize = tempsize + currentSize - size;
                    PUT(HEAD(temp), PACK(newsize, 0)); //set the header and footer of new free block
                    PUT(FOOT(temp), PACK(newsize, 0));
                    coalesce(temp);
                }
                return newptr;                      
            }           
            
            //if next is unallocated and combining next with this block would fufill new size requirement merge the blocks
            else if(next_alloc == 0 && (nextsize + currentSize) >= (size + DSIZE)){
                remove_block(NEXT(ptr)); //will be using the next block

                if (size <= DSIZE) //adjusting if necessary
                    size = DDSIZE;
                else
                    size =  DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
        
                // take up all space if a free block can't be made
                if((nextsize + currentSize) < (size + 2*DSIZE)) 
                    size = nextsize + currentSize;
                
                PUT(HEAD(oldptr), PACK(size, 1)); //set header and footer
                PUT(FOOT(oldptr), PACK(size, 1)); 
                    
                    //if new free block initialize it
                if((nextsize + currentSize) >= (size + DDSIZE)){ 
                    
                    newptr = NEXT(oldptr);
                    int newsize = nextsize + currentSize - size;        
                    PUT(HEAD(newptr), PACK(newsize, 0)); //set the new free block
                    PUT(FOOT(newptr), PACK(newsize, 0));
                    
                    coalesce(newptr);
                }
                return oldptr;                  
            }
            
            //if prev is free and prev + current is enough for new block
            else if (previous_alloc == 0 && (prevsize + currentSize) >= (size + DSIZE)){
                newptr = PREV(oldptr); //will be the address of expanded block
                    
                remove_block(PREV(oldptr)); //remove previous since we're using it
                    
                if (size <= DSIZE) //adjust
                    size = DDSIZE;
                else
                    size =  DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
        
                if((prevsize + currentSize) < (size + 2*DSIZE)) // if not big enough for new free block make new block take all space
                    size = prevsize + currentSize;
                
                PUT(HEAD(newptr), PACK(size, 1));  //reset for new size
                    
                copySize = GET_SIZE(HEAD(oldptr)); //calculate size to copy
                memcpy(newptr, oldptr, copySize);
                    
                PUT(FOOT(newptr), PACK(size, 1)); //would have gotten copied over
                
                if((prevsize + currentSize) >= (size + DDSIZE)){ //if there is a new block
                            
                    temp = NEXT(newptr);
                    
                    int newsize = prevsize + currentSize - size;
                    PUT(HEAD(temp), PACK(newsize, 0)); //set header and footer with remaining size
                    PUT(FOOT(temp), PACK(newsize, 0));
                    
                    coalesce(temp); //add the new block to free list
                    }
                    return newptr;      
                }
            //else, have to extend the heap set new pointer to newly allocated block of size
            newptr = mm_malloc(size);
            
            copySize = GET_SIZE(HEAD(oldptr)); //calculate size to copy
            if (size < copySize)
                copySize = size;
            memcpy(newptr, oldptr, copySize);
            mm_free(oldptr);
            return newptr;
    }
}

/* 
 * checkheap - checks:
 *      Is every block in the free list marked as free?
 *      Are there any contiguous free blocks that somehow escaped coalescing?
 *      Is every free block actually in the free list?
 *      Do the pointers in the free list point to valid free blocks?
 *      Do any allocated blocks overlap
 *      Do the pointers in a heap block point to valid heap addresses?
 */
static int mm_checkheap(void)  
{ 
    if (checkCoalesceAndFree() == 0){
        return 0;
    }
    if (checkFreeInList() == 0){
        return 0;
    }
    if (checkOverlap() == 0){
        return 0;
    }
    if (mm_valid_heap() == 0){
        return 0;
    }
    return 1;
}

/* check to see if pointers in heap block point to a valid heap address
    1: pointer has to be greater than prologue and less than epilogue (aka within the heap)
    2: pointer has to be aligned to 8 */
static int mm_valid_heap(void){
    char *heap_check;
    for(heap_check = NEXT(heap_listp); heap_check < epilogue_block; heap_check = NEXT(heap_check)) {
        if((HEAD(heap_check) < HEAD(NEXT(heap_listp))) || ((char *)GET(HEAD(heap_check)) > epilogue_block) || (GET_ALIGN(HEAD(heap_check)) != 0)) {
            printf("Error: current block does not point to a valid heap address: %p\n", heap_check);
            return 0;
        }
    }
    return 1;
}

/* 
 * checkCoalesceAndFree- 
 * Checks that no blocks escaped coalescing
 * Checks that the free list only contains free blocks
 */
static int checkCoalesceAndFree(void){
    char* current = list_head;
    int i;
    for (i = 0; i < free_count; i++){
        if (GET_ALLOC(HEAD(current)) || GET_ALLOC(FOOT(current))){
            return 0; //if either the head or footer are marked allocated
        }
        /* this part checks that the free block's next and prev blocks are allocated (did not escape coalesce) */
        if (NEXT(current) != 0 && !GET_ALLOC(HEAD(NEXT(current)))){
            return 0;  //if it has a next and it is free
        }
        if (PREV(current+WSIZE) != 0 && !GET_ALLOC(HEAD(PREV(current))))  {
            return 0;  //if it has a prev and it is free
        }
        current = (char *)GET(current+WSIZE);
    }
    return 1;
}

/*
*  checkOverlap - checks if any of the allocated blocks overlap each other
*/
static int checkOverlap(void){
    void *current = heap_listp; //pointer beinning of heap
    while(current != NULL && GET_SIZE(HEAD(current))!=0){  //goes through the whole heap until epilogue block
        if(GET_ALLOC(HEAD(current))){  //if it is allocated
            void *next = NEXT(current);  //get the address of the next block
            if (current + GET_SIZE(HEAD(current)) - WSIZE >= next)  //if current + size is greater than address of next, there is an overlap
                return 0;
        }
        current = NEXT(current);
    }
    return 1;
}
/*
*   checkFreeInList - checks that every free block of the heap is on the list.
*/
static int checkFreeInList(void){
    void *current = heap_listp; // pointer to the beginning of heap
    while (current != NULL && GET_SIZE(HEAD(current)) != 0){
        if (GET_ALLOC(HEAD(current)) == 0){ //if it finds a free block
            void *list = list_head;    //get the beginning of the list
            while (current != list){  //looks through the free list for the free block found
                list = (char *)GET(list+WSIZE);
                if (list == 0)  //reach the end of the free list
                    return 0;
            }
        }
        current = NEXT(current);
    }
    return 1;
}



