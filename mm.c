#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "team 5",
    "Juhee Lee",
    "juhee971204@gmail.com",
    "",
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 & 매크로 */
#define WSIZE 4              // word size
#define DSIZE 8              // double word size
#define CHUNKSIZE (1 << 12)  // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)
#define SEGREGATED_SIZE (20) // segregated list의 class 개수
#define MAX(x, y) (x > y ? x : y)

/* 가용 리스트를 접근/순회하는 데 사용할 매크로 */
#define PACK(size, alloc) (size | alloc)                              // size와 할당 비트를 결합, header와 footer에 저장할 값
#define GET(p) (*(unsigned int *)(p))                                 // p가 참조하는 워드 반환 (포인터라서 직접 역참조 불가능 -> 타입 캐스팅)
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))      // p에 val 저장
#define GET_SIZE(p) (GET(p) & ~0x7)                                   // 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_ALLOC(p) (GET(p) & 0x1)                                   // 할당 상태
#define HDRP(bp) ((char *)(bp)-WSIZE)                                 // Header 포인터
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 포인터

static char *heap_listp;                                // 클래스의 시작
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void splice_free_block(void *bp); // 가용 리스트에서 제거
static void add_free_block(void *bp);    // 가용 리스트에 추가
static int get_class(size_t size);

int mm_init(void)
{
    // 초기 힙 생성
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(heap_listp, 0);                                                    // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Header (크기: 헤더 1 + 푸터 1 + segregated list 크기)
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                             // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치
    heap_listp += (2 * WSIZE);
    if (extend_heap(4) == NULL)
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize = 16; // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    if (size == 0) // 잘못된 요청 분기
        return NULL;

    while (asize < size + DSIZE) // 요청받은 size에 8(헤더와 푸터 크기)를 더한 값을 2의 n승이 되도록 올림
    {
        asize <<= 1;
    }

    if ((bp = find_fit(asize)) != NULL) // 가용 블록 검색
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    // 적합한 블록이 없을 경우 힙확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    coalesce(bp);
}

// 기존에 할당된 메모리 블록의 크기 변경
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);
    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사
    mm_free(ptr);                  // 기존 블록 해제
    return newptr;
}

static void *extend_heap(size_t words)
{
    char *bp;
    if ((long)(bp = mem_sbrk(words * WSIZE)) == -1) // 힙 확장
        return NULL;
    PUT(HDRP(bp), PACK(words * WSIZE, 0)); // 새 빈 블록 헤더 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 에필로그 블록 헤더 초기화
    return coalesce(bp);                   // 병합 후 리턴 블록 포인터 반환
}

static void *coalesce(void *bp)
{
    add_free_block(bp);                                      // 현재 블록을 free list에 추가
    size_t csize = GET_SIZE(HDRP(bp));                       // 반환할 사이즈
    void *root = heap_listp + (SEGREGATED_SIZE + 1) * WSIZE; // 실제 메모리 블록들이 시작하는 위치
    void *left_buddyp;                                       // 왼쪽 버디의 bp
    void *right_buddyp;                                      // 오른쪽 버디의 bp

    while (1)
    {
        // 좌우 버디의 bp 파악
        if ((bp - root) & csize) // 현재 블록에서 힙까지의 메모리 합(bp - root)과 csize가 중복되는 비트가 있다면 현재 블록은 오른쪽 버디에 해당
        {
            left_buddyp = bp - csize;
            right_buddyp = bp;
        }
        else
        {
            right_buddyp = bp + csize;
            left_buddyp = bp;
        }

        // 양쪽 버디가 모두 가용 상태이고, 각 사이즈가 동일하면 (각 버디가 분할되어있지 않으면)
        if (!GET_ALLOC(HDRP(left_buddyp)) && !GET_ALLOC(HDRP(right_buddyp)) && GET_SIZE(HDRP(left_buddyp)) == GET_SIZE(HDRP(right_buddyp)))
        {
            splice_free_block(left_buddyp); // 양쪽 버디를 모두 가용 리스트에서 제거
            splice_free_block(right_buddyp);
            csize <<= 1;                            // size를 2배로 변경
            PUT(HDRP(left_buddyp), PACK(csize, 0)); // 왼쪽 버디부터 size만큼 가용 블록으로 변경
            add_free_block(left_buddyp);            // 가용 블록으로 변경된 블록을 free list에 추가
            bp = left_buddyp;
        }
        else
            break;
    }
    return bp;
}

static void *find_fit(size_t asize)
{
    int class = get_class(asize);
    void *bp;
    while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
    {
        bp = GET_ROOT(class);
        while (bp != NULL)
        {
            if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
                return bp;
            bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
        }
        class += 1;
    }
    return NULL;
}

static void place(void *bp, size_t asize) // 할당할 위치의 bp, 사용할 양
{
    splice_free_block(bp);             // free_list에서 해당 블록 제거
    size_t csize = GET_SIZE(HDRP(bp)); // 사용하려는 블록의 크기

    while (asize != csize) // 사용하려는 asize와 블록의 크기 csize가 다르면
    {
        csize >>= 1;                           // 블록의 크기를 반으로 나눔
        PUT(HDRP(bp + csize), PACK(csize, 0)); // 뒷부분을 가용 블록으로 변경
        add_free_block(bp + csize);            // 뒷부분을 가용 블록 리스트에 추가
    }
    PUT(HDRP(bp), PACK(csize, 1)); // 크기가 같아지면 해당 블록 사용 처리
}

// 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void splice_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class)); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

// 적합한 가용 리스트를 찾아서 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    GET_SUCC(bp) = GET_ROOT(class);     // bp의 해당 가용 리스트의 루트가 가리키던 블록
    if (GET_ROOT(class) != NULL)        // list에 블록이 존재했을 경우만
        GET_PRED(GET_ROOT(class)) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    GET_ROOT(class) = bp;
}

// 적합한 가용 리스트를 찾는 함수
int get_class(size_t size)
{
    int next_power_of_2 = 1;
    int class = 0;
    while (next_power_of_2 < size && class + 1 < SEGREGATED_SIZE)
    {
        next_power_of_2 <<= 1;
        class ++;
    }

    return class;
}
