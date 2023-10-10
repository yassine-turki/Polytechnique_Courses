/*
Followed the implementation given by the textbook

Create a prologue block and an epilogue footer for alignment considerations when starting the heap with mm_init.
The "payload" of the prologue block is referenced by the global variable heap_listp.
We will utilize this to identify the blocks in the heap.

Perform a first-fit search of our global_list (also known as the extended list) 
when malloc is called to locate a location that will fit. 
The block is allocated as soon as the right one is discovered. 
However, we split that block and add it to our list of free blocks 
if the size of the free block minus the size we are requesting is large enough 
to accommodate another block. If not, we allocate the desired malloc the full free block.

We simply release the block after freeing, 
but the coalescing issue is crucial in this case.
We verify the previous and next block of the current pointer in our 
coalesce method before coalescing the required blocks.

To check for consistency in the heap, we also created a heap checker. 
It only performs tests to ensure that the free list contains free blocks,
the heap pointers point to legitimate heap addresses, etc. 

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
    "The Lone Yassine",
    /* First member's full name */
    "Yassine Turki",
    /* First member's email address */
    "yassine.turki@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Basic constants and macros */

#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define ALIGNMENT 8

#define MAX(x, y) ((x) > (y)? (x) : (y)) 


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))  
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */

#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)   

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Macro for mm_check */
#define GET_ALIGN(p) (GET(p) & 0x7)


/* We define global variables */

static char *heap_listp = 0;  /* Pointer to first block */
char *free_list_head_ptr = 0; //list of free blocks
char *epilogue_block_ptr = 0; /* Pointer to epilogue block */
int num_free_blocks = 0; // Counter for number of free blocks

/* We define helper functions */


static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void add_block(void *bp);
static void delete_free_block(void *bp);
static int mm_check(void);

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }

    /* Prologue block */
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 

    /* Epilogue block */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    epilogue_block_ptr = (char *)(heap_listp + (3*WSIZE));  /*ptr useful for mm_check*/

    /* Set heap_listp to point to the start of the first block */
    heap_listp += (2*WSIZE);

    /* Initialize free list */

    free_list_head_ptr = 0; 
    num_free_blocks = 0; 

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL) {
        return -1;
    }

    return 0;
}


/*
Extends the heap with a new free block.
 */

static void *extend_heap(size_t words){
    char *bp;
    size_t size; 
    size = DSIZE * ((DSIZE + (DSIZE - 1) + words)/ DSIZE);
    if ((long)(bp = mem_sbrk(size)) == -1)    
        return NULL;
    //initialize free block HEAD and epilogue HEAD
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header*/
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp); 
}

/* 
 * mm_free:
 */

void mm_free(void *bp)
{
    /*Ignore spurious requests*/
    if(bp == NULL) {
        return ;
    }

    /*Get the size of the block*/
    size_t size = GET_SIZE(HDRP(bp)); 

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * Coalesce checks if coalescing with both prev and next blocks is possible (or only in one direction), 
 or cannot coalesce so we return the original block

 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { // Case 1: both prev and next blocks are allocated
        add_block(bp); // add the current block to the free list
    }

    else if (prev_alloc && !next_alloc) { // Case 2: next block is free, coalesce with current block
        void *next_bp = NEXT_BLKP(bp); // next block pointer
        delete_free_block(next_bp); // remove next block from the free list
        size += GET_SIZE(HDRP(next_bp)); // update current block size
        PUT(HDRP(bp), PACK(size, 0)); // update current block header
        PUT(FTRP(bp), PACK(size, 0)); // update current block footer
        add_block(bp); // add the coalesced block to the free list
    }
    
    else if (!prev_alloc && next_alloc) { // Case 3: prev block is free, coalesce with current block
        void *prev_bp = PREV_BLKP(bp); // prev block pointer
        delete_free_block(prev_bp); // remove prev block from the free list
        size += GET_SIZE(HDRP(prev_bp)); // update current block size
        PUT(HDRP(prev_bp), PACK(size, 0)); // update prev block header
        PUT(FTRP(bp), PACK(size, 0)); // update current block footer
        bp = prev_bp; // move the block pointer to the start of the prev block
        add_block(bp); // add the coalesced block to the free list
    }

    else { // Case 4: both prev and next blocks are free, coalesce all three blocks
        void *prev_bp = PREV_BLKP(bp); // prev block pointer
        void *next_bp = NEXT_BLKP(bp); // next block pointer
        delete_free_block(prev_bp); // remove prev block from the free list
        delete_free_block(next_bp); // remove next block from the free list
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp)); // update current block size
        PUT(HDRP(prev_bp), PACK(size, 0)); // update prev block header
        PUT(FTRP(next_bp), PACK(size, 0)); // update next block footer
        bp = prev_bp; // move the block pointer to the start of the prev block
        add_block(bp); // add the coalesced block to the free list
    }
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) 
{
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    // ignore spurious requests
    if (size == 0) {
        return NULL; 
    }
/* Adjust block size to include overhead and alignment reqs. */
   asize = size <= DSIZE ? 2*DSIZE : ALIGN(size + DSIZE); 


    // We look for a free block that fits
    if (num_free_blocks == 0){
        bp = NULL;
    }
    bp = free_list_head_ptr; //point to the beginning of free list
    int i;
    for (i = 0; i < num_free_blocks; i++){ //iterate through the list for a free block
        if (asize <= GET_SIZE(HDRP(bp))){
             break;
        }
        bp = (char *) GET(bp+WSIZE); //go to the next free block
    }
    if (bp != NULL) {
        place(bp, asize); // place the requested block into the free block
        return bp;
    }

    // no free block found, extend the heap by the max of the requested size and CHUNKSIZE
    extendsize = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extendsize);
    if (bp == NULL) {
        return NULL; // heap extension failed
    }

    // place the requested block into the newly allocated block
    place(bp, asize);
    return bp;
}


/* 
 * place - Place a block of asize and split if the remainder of block is at least 16 
 */
static void place(void *bp, size_t asize) {
    size_t block_size = GET_SIZE(HDRP(bp));
size_t remaining_size = block_size - asize;
if(remaining_size<=2*DSIZE){
        /* Use the whole block */
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
        delete_free_block(bp);  // Remove the allocated block from the free list
    
}
    else {
        /* Split the block and use only the required space */
        delete_free_block(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void* next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remaining_size, 0));
        PUT(FTRP(next_bp), PACK(remaining_size, 0));
        add_block(next_bp);  // Add the newly split block to the free list
    } 
}


/*
* delete_free_block- removes block from the free list
*/
static void delete_free_block(void *bp){
    int prev=GET(bp);
    int next=GET(bp+WSIZE);

    if (prev == 0 && next == 0){ /*Case 1: We we do not have prev and next*/
        free_list_head_ptr = 0;
    } 
    else if (prev != 0 && next == 0){ /*Case 2: We have prev but not next => end of list*/
        PUT(((char *)prev + WSIZE), 0); //set the prev block's next to 0
    }
    else if (prev == 0 && next != 0){ /*Case 3: We don't have prev but we have next => beginning of list*/
        free_list_head_ptr = (char *)next;
        PUT((char *)next, 0); //set next block's prev to 0
    } 
    
    else{ 
        PUT(((char *)prev + WSIZE), next);   //set prev block's next to point to bp's next
        PUT(((char *)next), prev); //set next's prev to prev
    }
    num_free_blocks-=1;
}

/*
* add - sets the new free block to the first of the list
*/
static void add_block(void *bp){
    /*Increase the count of free blocks*/
    num_free_blocks+=1;

    if ((num_free_blocks) != 1){ //if list is not empty
     // Add the block to the beginning
        PUT(((char *)free_list_head_ptr), (int)bp); //Set the previous block's next to point to the new block
        PUT(bp, 0); // Set the new block's previous to NULL
        PUT(bp + WSIZE, (int)free_list_head_ptr); // Set the new block's next to point to the current head of the list
        free_list_head_ptr = bp;  // Set the head of the list to point to the new block
    }
    else{
         // If the list is empty, set the head of the list to the new block and initialize it
        free_list_head_ptr = bp;
        PUT(bp, 0);  // Set the previous and next pointers of the new block to NULL
        PUT(bp+WSIZE, 0);
        return;
    
    }
}




/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

void *mm_realloc(void *ptr, size_t size)
{
    size_t oldSize, newSize;
    void *newPtr;

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL) {
        return mm_malloc(size);
    }

    oldSize = GET_SIZE(HDRP(ptr)) - DSIZE;
    newSize = size + DSIZE;

    if (newSize <= oldSize) {
        size_t nextAlloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        size_t nextSize = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        size_t combinedSize = oldSize + nextSize;

        if (!nextAlloc && combinedSize >= newSize) {
            delete_free_block(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(combinedSize, 1));
            PUT(FTRP(ptr), PACK(combinedSize, 1));
            return ptr;
        }
    }

    newPtr = mm_malloc(size);
    if (newPtr == NULL) {
        return NULL;
    }

    memcpy(newPtr, ptr, oldSize < size ? oldSize : size);
    mm_free(ptr);
    return newPtr;
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



// static int mm_check(void)  
// { 

// /*
// Check that every free block is contained in the free list
// */

//     void *currentptr = heap_listp; // pointer to the beginning of heap
//     while (currentptr != NULL && GET_SIZE(HDRP(currentptr)) != 0){
//     if (GET_ALLOC(HDRP(currentptr)) == 0){ //if it finds a free block
//         void *list = free_list_head_ptr;    //get the beginning of the list

//         // iterate through the free list until we find the free block found in the outer loop,
//         // or until we reach the end of the list
//         for (; list != currentptr && list != NULL; list = (char *)GET(list + WSIZE));
//         if (list == NULL) {
//             fprintf(stderr,"Free block was not found in free list\n");
//             return 0;
//         }
//     }

//     currentptr = NEXT_BLKP(currentptr); // move on to the next block in the heap
// }

//     /*
// *  We check if the allocated blocks are overlapping
// */
//     currentptr = heap_listp; //Start by begginning of heap
//     for(; currentptr != NULL && GET_SIZE(HDRP(currentptr))!=0; currentptr = NEXT_BLKP(currentptr)){  //goes through the whole heap until epilogue block
//         if(GET_ALLOC(HDRP(currentptr))){  //if it is allocated
//             void *next = NEXT_BLKP(currentptr);  //get the address of the next block
//             if (currentptr + GET_SIZE(HDRP(currentptr)) - WSIZE >= next){  //if current + size is greater than address of next, there is an overlap
//              fprintf(stderr,"Overlapping occurs for block starting at adress: %p\n", currentptr);
//                 return 0;
//             }
//         }
//     }

// /* 
// Check that no blocks escaped coalescing and that the free list does not contain allocated blocks
//  */
//     int i=0;
//     char* ptr = free_list_head_ptr;
//     while (ptr != NULL && i < num_free_blocks){
//         if (GET_ALLOC(HDRP(ptr))){
//              fprintf(stderr,"Head is marked as allocated!");
//              return 0;
//         }
//          if(GET_ALLOC(FTRP(ptr))){
//             fprintf(stderr,"Footer is marked as allocated!");
//             return 0;
//         }

//         /* Checking if current free block is between allocted blocks or not */
//         if (PREV_BLKP(ptr+WSIZE) != 0 && !GET_ALLOC(HDRP(PREV_BLKP(ptr))))  {
//             fprintf(stderr,"Block at adress: %p has a free block behind it!",ptr);
//             return 0;  
//         }

//         if (NEXT_BLKP(ptr) != 0 && !GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){
//             fprintf(stderr,"Block at adress: %p has a free block in front!",ptr);
//             return 0;  
//         }
//         ptr = (char *)GET(ptr+WSIZE); //Move to next free block
//         i++;
//     }

//     // Checking if heap is valid, meaning we check if pointers in heap block point to a valid heap address
//     //We check alignment, and we check if a pointer is greater than the prologue and less than epilogue, to make sure it is in the heap4
//     char *heap_check;
//     for(heap_check = NEXT_BLKP(heap_listp); heap_check < epilogue_block_ptr; heap_check = NEXT_BLKP(heap_check)) {
//         if((GET_ALIGN(HDRP(heap_check)) != 0) || (HDRP(heap_check) < HDRP(NEXT_BLKP(heap_listp))) || ((char *)GET(HDRP(heap_check)) > epilogue_block_ptr)) {
//             fprintf(stderr,"Adress of block is not valid (not in heap): %p\n", heap_check);
//             return 0;
//         }
//     return 1;
// }
// return 1;
// }

