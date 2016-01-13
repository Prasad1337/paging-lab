#include <stdlib.h>
#include <stdio.h> 
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

#include "simulator.h"


#define HSIZE (1 << 11)
#define MAX_PAGE_ALLOC 40
#define REALLOC_BASE 50
#define REALLOC_INTERVAL (REALLOC_BASE*100)
#define HPLUS_ONE(_element) ( (_element < (HSIZE-1) )? (_element+1) : 0)
#define HMINUS_ONE(_element) ( (_element == 0 )? (HSIZE-1) : (_element-1) )


static int tick = 0; // artificial time


struct phist_record {
    int page;
    int fault;
};

struct phist {
    struct phist_record records[HSIZE];
    int head;
    int tail;
};


static struct phist phist_arr[MAXPROCESSES];
static int pg_alloc[MAXPROCESSES];
static int proc_faults[MAXPROCESSES];
static int proc_susp[MAXPROCESSES];
static int proc_pset[MAXPROCESSES][MAXPROCPAGES];
static int proc_last_evict[MAXPROCESSES];
static int proc_last_unsat[MAXPROCESSES];
static int proc_last_pagein[MAXPROCESSES];

static int timestamps[MAXPROCESSES][MAXPROCPAGES];


static void inc_head(struct phist *ph) {
    int tmp;

    tmp = HPLUS_ONE(ph->head);
    if(tmp == ph->tail)
        ph->tail = HPLUS_ONE(ph->tail);

    ph->head = tmp;
}

void phist_init(struct phist *ph) {
    ph->head = 0;
    ph->tail = 0;
}

void phist_push(struct phist *ph, const struct phist_record *ph_r) {
    ph->records[ph->head] = *ph_r;
    inc_head(ph);
}

void phist_len(const struct phist *ph, int *len) {
    int tmp;

    tmp = HPLUS_ONE(ph->head);
    if(tmp == ph->tail)
        *len = HSIZE;
    else
        *len = (ph->head - ph->tail) + 1;
}

void phist_at(const struct phist *ph, int t, struct phist_record *ph_r) {
    int len, i, ptr;
    
    phist_len(ph, &len);
    assert(t >= 0 && t < len);

    ptr = ph->head;
    for(i = 0; i < t; i++) {
        ptr = HMINUS_ONE(ptr);
    }

    *ph_r = ph->records[ptr];
}

void phist_fault_sum(const struct phist *ph, int *sum) {
    int ptr;

    *sum = 0;
    for(ptr = ph->tail; ptr != ph->head; ptr = HPLUS_ONE(ptr) ) {
        *sum += (ph->records[ptr].fault == 1);
    }
}

void phist_working_set(const struct phist *ph, int *pset, size_t psize) {
    int ptr;
    unsigned int i;
    
    for(i = 0; i < psize; i++) {
        pset[i] = 0;
    }
    
    for(ptr = ph->tail; ptr != ph->head; ptr = HPLUS_ONE(ptr) ) {
        pset[ph->records[ptr].page] = 1;
    } 
}

void phist_working_set_and_fault_sum(const struct phist *ph, int *pset, size_t psize, int *sum) {
    int ptr;
    unsigned int i;
    
    for(i = 0; i < psize; i++) {
        pset[i] = 0;
    }
    *sum = 0;

    for(ptr = ph->tail; ptr != ph->head; ptr = HPLUS_ONE(ptr) ) {
        pset[ph->records[ptr].page] = 1;
        *sum += (ph->records[ptr].fault == 1);
    } 
}

void phist_print_records(const struct phist *ph) {
    int ptr;

    for(ptr = ph->tail; ptr != ph->head; ptr = HPLUS_ONE(ptr) ) {
        printf("%d ", ph->records[ptr].page);       
    }

}


static size_t pages_alloc(Pentry q[MAXPROCESSES], int proc) {
    int page;
    size_t amt = 0;

    for(page = 0; page < MAXPROCPAGES; page++) {
        if(q[proc].pages[page])
            amt++;
    }

    return amt;
}

static void timestamps_init() {
    int proc, page;

    for(proc = 0; proc < MAXPROCESSES; proc++)
        for(page = 0; page < MAXPROCPAGES; page++)
            timestamps[proc][page] = 0; 

}

static void lru_page(Pentry q[MAXPROCESSES], int proc, int tick, int *evictee) {
    int page;
    int t;

    *evictee = -1;

    t = tick+1;  

    for(page = 0; page < MAXPROCPAGES; page++) {
        if(!q[proc].pages[page])
            continue;

        if(timestamps[proc][page] < t) {
            t = timestamps[proc][page];
            *evictee = page;

            if(t <= 1)
                break;
        }
    }           

    if(*evictee < 0) {
        printf("page for process %d w/ %u active pages not found with age < %u\n", proc, (unsigned int) pages_alloc(q, proc), tick);
        fflush(stdout);
    }
}



struct proc_fault_pair {
    int proc;
    int faults;
};

static int cmp_pfp(const void * pfp1, const void * pfp2 ) {
    struct proc_fault_pair *p1, *p2;
    p1 = (struct proc_fault_pair *) pfp1;
    p2 = (struct proc_fault_pair *) pfp2;

    if(p1->faults < p2->faults)
        return -1;
    else if(p1->faults == p2->faults)
        return 0;
    else
        return 1;
}

static void pred_pageit(Pentry q[MAXPROCESSES], uint32_t tick) {

    int proc, page, evicted, i;
    struct phist_record ph_r;
    int unsat[MAXPROCESSES];
    int amt_unsat = 0;
    int allocated[MAXPROCESSES];
    int faults[MAXPROCESSES];
    int pset_sizes[MAXPROCESSES];
    int pages_freed = 0;
    int free_phys = 100;
    
    for(i = 0; i < MAXPROCESSES; i++)
        unsat[i] = -1;

    for(proc = 0; proc < MAXPROCESSES; proc++) {
        if(!q[proc].active)
            continue;

        allocated[proc] = pages_alloc(q, proc);
        free_phys -= allocated[proc];
        
        if(proc_susp[proc] > 0) 
            continue;
        
    
        page = q[proc].pc/PAGESIZE;
  
        timestamps[proc][page] = tick;

        
        ph_r.page = page;

        if(q[proc].pages[page]) {
            ph_r.fault = 0;
            phist_push(&phist_arr[proc], &ph_r);
            continue;
        }

        ph_r.fault = 1;
        phist_push(&phist_arr[proc], &ph_r);

        phist_working_set_and_fault_sum(&phist_arr[proc], proc_pset[proc], MAXPROCESSES, &faults[proc]);
        
        pset_sizes[proc] = 0;           
        for(i = 0; i < MAXPROCESSES; i++) {
            if(proc_pset[proc][i] == 1)
                pset_sizes[proc]++;
        }

        if(pset_sizes[proc] < allocated[proc]) 
            for(i = 0; i < MAXPROCPAGES; i++) 
                if(q[proc].pages[i] && proc_pset[proc][i] == 0) {
                    pageout(proc, i);
                    pages_freed++;
                }

        if( pagein(proc, page) ) {
            proc_last_pagein[proc] = tick;
            free_phys--;
            continue;
        }   

        if(allocated[proc] < 1 && (tick - proc_last_unsat[proc]) < 100 )
            continue;

        unsat[proc] = page;
        amt_unsat++;
        proc_last_unsat[proc] = tick;
    }

    assert(free_phys >= 0);
    
    if(amt_unsat > 0) {     
        
        if(pages_freed >= amt_unsat)
            return;

        struct proc_fault_pair thrash_list[MAXPROCESSES];
        for(i = 0; i < MAXPROCESSES; i++) {
            thrash_list[i].proc = i;
            thrash_list[i].faults = ((q[i].active && (proc_susp[i] == 0) )? faults[i] : -1);
        }

        qsort(thrash_list, MAXPROCESSES, sizeof(struct proc_fault_pair), cmp_pfp);
        
        int k;
        for(k = 0; k < MAXPROCESSES; k++) {
            if((tick - proc_last_pagein[thrash_list[MAXPROCESSES-1-k].proc]) > 100 && thrash_list[MAXPROCESSES-1-k].faults >= 2048 && allocated[thrash_list[MAXPROCESSES-1-k].proc] > 0) {
                for(i = 0; i < MAXPROCPAGES; i++) 
                    if(q[thrash_list[MAXPROCESSES-1-k].proc].pages[i]) {
                        pageout(thrash_list[MAXPROCESSES-1-k].proc, i);
                        pages_freed++;
                    }
    
                if(unsat[thrash_list[MAXPROCESSES-1-k].proc] == 1)
                    pages_freed++;
                
                fflush(stdout);
                proc_susp[thrash_list[MAXPROCESSES-1-k].proc] = tick;   
            }

            if(pages_freed >= amt_unsat)
                return;
        }

        for(proc = 0; proc < MAXPROCESSES; proc++) {
            if(unsat[proc] < 0)
                continue;

            if(allocated[proc] < 1)
                continue;
                
            lru_page(q, proc, tick, &evicted);
            if(!pageout(proc, evicted) ) {

            }
            pages_freed++;
            
            if(pages_freed >= amt_unsat)
                break;
        }
    } /* amt_unsat > 0 */
    else if(free_phys > 0) {

        for(proc = 0; proc < MAXPROCESSES; proc++) {
            int wset_size = 0;
            if(proc_susp[proc] == 0)
                continue;

            if( tick - proc_susp[proc] < 500 )
                continue;
                
            if(free_phys < 1)
                break;

            for(i = 0; i < MAXPROCPAGES; i++) {
                wset_size += (proc_pset[proc][i] != 0);
            }

            if(wset_size > free_phys)
                continue;

            proc_susp[proc] = 0;
            for(i = 0; i < MAXPROCPAGES; i++) {
                if(proc_pset[proc][i]) {
                    if( !pagein(proc, i) )
                        free_phys = 0;
                        
                    free_phys--;
                }
            }

        } 
    } 
    
}

void pageit(Pentry q[MAXPROCESSES]) {
    
    if(tick < 1) {
        int i;
        
        timestamps_init();
        for(i = 0; i < MAXPROCESSES; i++) {
            phist_init(&phist_arr[i]);
            pg_alloc[i] = 20;
            proc_faults[i] = 0;
            proc_susp[i] = 0;
            proc_last_evict[i] = 0;
            proc_last_unsat[i] = 0;
            proc_last_pagein[i] = 0;
        }   

        tick = 1;
    }   
    
    pred_pageit(q, tick);
    tick++;
}
