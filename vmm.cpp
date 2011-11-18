/* HW4 CS538 Vmm Sim Implementation, Fall 2011, Xiaolong Cheng
 * environment: Ubuntu 10.4  with g++ */

#include<cstdio>  
#include<cstdlib>
#include<cstring>
#include<cmath>
#include<stack>
#include<string>
#include<iostream>
using namespace std;

#define MEM_COST 20  //cycles for mem access with vmm
#define SWAP_COST 50000 //cycles for swaps
#define PAGE_SIZE (4*1024)  //page size
#define ADDR_SIZE 32
#define N_ENTRY_PER_PAGE 1024  //max entry in a page
#define OFFSET_BITS_SIZE 12 //2^12 = 4KB
#define PT_BITS_SIZE 10
#define PT_MASK 0x3ff000 //0000 0000 0011 1111 1111 0000 0000 0000
#define PAGE_OFFSET_MASK 0xfff //0000 0000 0000 0000 0000 1111 1111 1111
#define ENTRY_SIZE 4 //bytes
#define MIN_NUM_FRAMES 3 //frames can not be less than 3


/* by default, debug, trace and version command are all disabled */

bool _DEBUG = false;//for debug info, printing the vmm state
bool _TRACE = false;
bool _VERSION = false;

//DEV_DEBUG is used by developers
bool DEV_DEBUG = false;

// default frame number is 10
int N_frames =10;

// LIFO for debug information, each is packed as string
stack<string> debugInfo;

/* this struct keep track of the statistics */
struct vmm_status{
  int numAccess;
  int numRead;
  int numWrite;
  int numCycle;
  int numCyclesWithoutVmm;
  int numSwapIn;
  int numSwapOut;
  int numReplacement;
  int numPDEntry;

  int numPT;         // # of PTs ever allocated
  int numPTMax;      // maximum PTs resident in mem at one moment
  int numPTcurrent;  //# of PTs currently in mem

  int numPageTotal;  //#of user pages total
  int numPageMax;
  int numPageCurrent; //# of pages currently resident in mem

  int numFrame;
} stat ={0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

void printStat(){
  //prepare the data for printing
  stat.numAccess = stat.numRead+ stat.numWrite;
  stat.numCyclesWithoutVmm= stat.numAccess * MEM_COST;
  stat.numFrame=N_frames;
  printf("--------------STATISTICS---------------\n");
  printf("Access: %d\n Reads: %d\n Writes: %d\n Cycles: %d\n Cycles Without VMM :%d\n Swap ins: %d\n Swap outs: %d\n Pure Replacements: %d\n PD entries used: %d\n PT total: %d\n PT max: %d\n user pages total: %d\n user pages max: %d\n Physical page frames: %d\n",stat.numAccess, stat.numRead, stat.numWrite, stat.numCycle, stat.numCyclesWithoutVmm, stat.numSwapIn, stat.numSwapOut, stat.numReplacement, stat.numPDEntry, stat.numPT, stat.numPTMax, stat.numPageTotal, stat.numPageMax, stat.numFrame);
  printf("-----------END OF STATISTICS-----------\n\n");
}



/* hexToInt() converts hex char to decimal int */
int hexToInt(char* input){ 
    int x = 4;
    int size;
    size = strlen(input);
    // size =8;
    int result =0;
   
    for (int i = 0; i < size; i++)
    {
        if (input[i] =='0') {
	    result += 0;
        }
        else if (input[i] =='1') {
            result +=  pow(16,size-1-i);
        }    
        else if (input[i] =='2') {
            result += 2* pow(16,size-1-i);
        }    
        else if (input[i] =='3') {
            result += 3* pow(16,size-1-i);
        }    
        else if (input[i] =='4') {
            result += 4* pow(16,size-1-i);
        }    
        else if (input[i] =='5') {
            result += 5* pow(16,size-1-i);
        }    
        else if (input[i] =='6') {
            result += 6* pow(16,size-1-i);
        }    
        else if (input[i] =='7') {
            result += 7* pow(16,size-1-i);
        }    
        else if (input[i] =='8') {
            result += 8* pow(16,size-1-i);
        }
        else if (input[i] =='9') {
            result += 9* pow(16,size-1-i);
        }
        else if (input[i] =='a') {    
            result += 10* pow(16,size-1-i);
        }
        else if (input[i] =='b') {
            result += 11* pow(16,size-1-i);
        }
        else if (input[i] =='c') {
            result += 12* pow(16,size-1-i);
        }
        else if (input[i] =='d') {    
            result += 13* pow(16,size-1-i);
        }
        else if (input[i] =='e'){    
            result += 14* pow(16,size-1-i);
        }
        else if (input[i] =='f') {
            result += 15* pow(16,size-1-i);
        }
    }

    return result;
}



// pdbr is the pointer to the PD frame
struct page*  pdbr = NULL;

// page_frames is an array of page frame pointers
struct page** page_frames;


//represent disk space as a linked list, easy to be traversed 
struct diskblock{
  struct page* page;
  struct diskblock* next;
};
struct diskblock* disk = NULL;//head of the linked list of blocks/pages


struct entry{
  //each entry contains an address for next level page
  struct page* frame_addr; 
  //address of page on disk, if any
  struct diskblock* disk_addr;

  bool on_disk;
  bool dirty;
  bool valid;
};

/* a page can be PD,PT and user pages, for user pages, there is real data,
   but the data is uninteresting in simulation so we don't care */
struct page{
  struct entry entries[N_ENTRY_PER_PAGE];
};

/* retrieve the index of a frame given an address of page */

int find_frame_index(struct page* pg){
  for(int i=0;i<N_frames;++i){
    if(page_frames[i]==pg){
      if(DEV_DEBUG)printf("returning frame index %d\n",i);
      return i;
    }
  }
  fprintf(stderr,"page frame not found!\n");
  exit(1);
}


  /* to allocate new disk space */
 struct diskblock* allocDiskBlock(){
    struct diskblock* dblk= (diskblock*)malloc(sizeof(struct diskblock));
    if(!dblk){
      fprintf(stderr,"allocDiskBlock: Not enough memory!\n");
      exit(1);
    }
    if(DEV_DEBUG)printf("allocated new disk block %p \n",dblk);
    return dblk;
 }


  /*swap in a page from disk to given frame index */
 void swapIn(struct diskblock* disk, int frameIdx){
    if(DEV_DEBUG)printf("Swap in page %d from disk %p \n",frameIdx,disk);
    page_frames[frameIdx]=disk->page;
    stat.numCycle +=SWAP_COST;
    stat.numSwapIn++;
 }

  /* swap out a page to disk */
 void swapOut(struct entry* e, struct page* frame, struct diskblock *dblk){
    dblk->page = frame;
    dblk->next = disk;//build up the list...
    disk = dblk;
    e->disk_addr=dblk;
    stat.numCycle+=SWAP_COST;
    if(DEV_DEBUG) printf("Swap out %p to %p \n",frame,dblk);
    stat.numSwapOut++;
 }



/* create a new page in page frames with index idx */
void new_page(int idx){
  page_frames[idx]=(page*)calloc(1,sizeof(struct page));
  if(DEV_DEBUG)printf("new page at page_frames[%d]\n",idx);
  if(!page_frames[idx]){
    fprintf(stderr,"not enough memory for newing a page!\n");
    exit(1);
  }
}


/* allocate an empty page frame and return its index */
/* states of page frames are maintained in this function too*/
int alloc_page_frame(){
  int result;

  //check if free page frame available
  for(int i=0; i<N_frames;++i){
    if(page_frames[i]==NULL){
      if(DEV_DEBUG)printf("found unused page frame %d\n",i);
      return i;
    }
  }//end-for


  //maintain the list of page frames, do swap out, update, etc...

  //eviction follows the following order:
  /* unmodified userpage > modified userpage > unmodified page table > modified
     page table */

  struct page *modifiedUP=NULL, *unmodifiedPT=NULL, *modifiedPT=NULL;
  struct entry *mup_PTEntry=NULL, *mup_PDEntry=NULL,
    *upt_PDEntry=NULL, *mpt_PDEntry=NULL;

  for(int i=0; i<N_ENTRY_PER_PAGE;++i){
    struct entry* pdEntry= &pdbr->entries[i];
    // if in memory
    if(pdEntry->valid){
      struct page* PT = pdEntry->frame_addr;
      
      if(pdEntry->dirty && !modifiedPT){
	if(DEV_DEBUG)printf("found modified page table frame--codeline260 \n");
	modifiedPT=PT;
	mpt_PDEntry=pdEntry;
	}
      
      if(!pdEntry->dirty && !unmodifiedPT){
	if(DEV_DEBUG)printf("found unmodified page table frame\n");
	unmodifiedPT=PT;
	upt_PDEntry=pdEntry;
      }
      
      for(int j=0;j<N_ENTRY_PER_PAGE;++j){
	struct entry* ptEntry = &PT->entries[j];
	//if in memory
	if(ptEntry->valid){
	  struct page* userPage = ptEntry->frame_addr;

	  if(ptEntry->dirty && !modifiedUP){
	    if(DEV_DEBUG)printf("found modified user page \n");
	    modifiedUP=userPage;
	    mup_PTEntry=ptEntry;
	    mup_PDEntry=pdEntry;
	  }

	  if(!ptEntry->dirty){
	    // the best option
	    if(DEV_DEBUG)printf("found unmodified user page frame! \n");
	    if(!ptEntry->on_disk){
	      struct diskblock* dblk = allocDiskBlock();
	      swapOut(ptEntry,userPage,dblk);
	      stat.numPageCurrent--;
	      ptEntry->on_disk=true;
	    }else {
	      stat.numReplacement++;
	    }
	    ptEntry->valid=false;
	    pdEntry->dirty=true;
	    
	    return find_frame_index(userPage);
	  }
	}
      }
    }
  }

  if(modifiedUP){
    //exist modified user page
    struct diskblock* dblk =mup_PTEntry->disk_addr;
    if(!mup_PTEntry->on_disk){
      dblk=allocDiskBlock();
      mup_PTEntry->on_disk = true;
    }
    swapOut(mup_PTEntry,modifiedUP,dblk);
    stat.numPageCurrent--;
    mup_PTEntry->valid = false;
    mup_PDEntry->dirty= true;
    if(DEV_DEBUG)printf("returning modified user page \n");
    return find_frame_index(modifiedUP);
  }

  if(unmodifiedPT){//exists unmodified PT
  
    if(!upt_PDEntry->on_disk){
      struct diskblock* dblk=allocDiskBlock();
      swapOut(upt_PDEntry,unmodifiedPT,dblk);
      upt_PDEntry->on_disk=true;
    } else{
      stat.numReplacement++;
    }
    stat.numPTcurrent--;
    upt_PDEntry->valid = false;
    if(DEV_DEBUG) printf(" returning unmodified page table\n");
    return find_frame_index(unmodifiedPT);
  }

  
  if(modifiedPT){//exists modified page table
    struct diskblock* dblk = mpt_PDEntry->disk_addr;
    
    if(!mpt_PDEntry->on_disk){
      dblk=allocDiskBlock();
      mpt_PDEntry->on_disk=true;
    }
    swapOut(mpt_PDEntry,modifiedPT, dblk);
    stat.numPTcurrent--;
    mpt_PDEntry->valid = false;
    if(DEV_DEBUG) printf("returning modified page table \n");
    return find_frame_index(modifiedPT);
  }

  //just in case..
  fprintf(stderr, "internal error!! \n");
  exit(1);
    
}

/* extract index in PD from a virtual address */
int getPDindex(int addr){
  return (addr>>22); //get leftmost 10 bits
}

/* extract index in PT from a virtual address */
int getPTindex(int addr){
  return (addr& PT_MASK)>>12; // get second 10 bits
}

/* extract page offset */
int getPageOffset(int addr){
  return addr&PAGE_OFFSET_MASK;
}


class vmmsim{
public:
  //constructor, initialize configurations
  vmmsim(){
    //allocate an array of page frames
    page_frames = (page**) calloc(N_frames, sizeof(struct page*));

    //initialize PD
    int frameIdxOfPD = alloc_page_frame();
    new_page(frameIdxOfPD);
    pdbr = page_frames[frameIdxOfPD];

    //TODO:
    // maybe more initialization...
    
  }

  ~vmmsim(){//destructor, do cleaning-up   
    free(page_frames);// free the array of frame pointers
    //now free the pages
    for(int i=0;i<N_frames;++i){
      struct entry* pdEntry=&pdbr->entries[i];
      
      if(pdEntry->valid || pdEntry->on_disk){
	struct page* PT = pdEntry->frame_addr;
	for(int j=0;j<N_frames;++j){
	  struct entry* ptEntry=&PT->entries[j];
	  //if page exists
	  if(ptEntry->valid || ptEntry->on_disk){
	    free(ptEntry->frame_addr);
	  }
	}//end-for
	free(PT);
      }
    }//end-for

    //free disk blocks
    struct diskblock* ptr=disk;
    struct diskblock* next;
    while(ptr){
      next=ptr->next;
      free(ptr);
      ptr=next;
    }
    
  }

  //function to log vmm status/debug info
  void logDebugInfo(){
    string log;
    log.append("\n-vmm state-\n");
    for(int i=0;i<N_ENTRY_PER_PAGE;++i){
      struct entry* pdEntry = &pdbr->entries[i];
      if(pdEntry->valid||pdEntry->on_disk){//print PD states
	char buffer1[80];
	sprintf(buffer1,"[PD] entry %d - valid: %d, dirty: %d, on_disk:%d \n",i,pdEntry->valid, pdEntry->dirty,pdEntry->on_disk);
	log.append(buffer1);
	struct page* PT=pdEntry->frame_addr;
	for(int j=0;j<N_ENTRY_PER_PAGE;++j){
	  struct entry* ptEntry=&PT->entries[j];
	  if(ptEntry->valid||ptEntry->on_disk){//print PT states
	    //struct page* pg= ptEntry->frame_addr;
	    char buffer2[80];
	    sprintf(buffer2,"[PT] entry %d - valid: %d, dirty: %d, on_disk: %d \n",j, ptEntry->valid, ptEntry->dirty, ptEntry->on_disk);
	    log.append(buffer2);
	  }
	}//end-for(N_ENTRY_PER_PAGE)
      }
    }//end-for(N_ENTRY_PER_PAGE)
    //  cout<<log;
    
    debugInfo.push(log); //push log(string) to stack for LIFO output
  }//end-func

  /* this function takes care of the read operation */
  void read(int addr){

    // printf("int addr is %d\n",addr);
    
    int ndxPD= getPDindex(addr);
    int ndxPT= getPTindex(addr);
    int pgOffset= getPageOffset(addr);
    
    struct entry* pdEntry= &pdbr->entries[ndxPD];//TRICKY here
    
    stat.numCycle+=MEM_COST;//INCREASE COST ___________reading PD
    if(!pdEntry->valid){// if not valid
      //PT page fault
      if(DEV_DEBUG)printf("PT page fault\n");
      
      int freePageFrameNdx=alloc_page_frame();

      if(pdEntry->on_disk){
	if(DEV_DEBUG)printf("PT page on disk, swapping in..\n");
	swapIn(pdEntry->disk_addr, freePageFrameNdx);
      } else {
	if(DEV_DEBUG)printf("PT page not on disk, create new PT page \n");
	new_page(freePageFrameNdx);
	pdEntry->frame_addr = page_frames[freePageFrameNdx];
	stat.numPDEntry++;
      }

      stat.numPT++;
      stat.numPTcurrent++;
      if(stat.numPTcurrent>stat.numPTMax) stat.numPTMax=stat.numPTcurrent;
      
      pdEntry->valid= true;
    }// end if not valid

    else {
      if(DEV_DEBUG)printf("PT page found\n");
    }

    struct page* PT= pdEntry->frame_addr;
    struct entry* PTEntry = &PT->entries[ndxPT];//

    stat.numCycle+=MEM_COST;//INCREASE COST________reading PT
    if(!PTEntry->valid){
      //user page fault
      if(DEV_DEBUG)printf("User page fault\n");
 
      int freePageFrameNdx=alloc_page_frame();
      if(PTEntry->on_disk){
	if(DEV_DEBUG)printf("user page on disk, swapping in.. \n");
	swapIn(PTEntry->disk_addr, freePageFrameNdx);
      } else{
	if(DEV_DEBUG)printf("user page not on disk: create new user page \n");
	new_page(freePageFrameNdx);
	PTEntry->frame_addr=page_frames[freePageFrameNdx];
      }

      stat.numPageTotal++;
      stat.numPageCurrent++;
      if(stat.numPageCurrent>stat.numPageMax) stat.numPageMax=stat.numPageCurrent;
      
      PTEntry->valid = true;
      pdEntry->valid = true;
    } else{
      if(DEV_DEBUG) printf("user page found\n");
    }
    
    // accessing user page
    struct page* userPage = PTEntry->frame_addr;
    stat.numCycle+=MEM_COST;//INCREASE COST________reading user page

    
    stat.numRead++;
    if(_DEBUG) logDebugInfo(); //take notes of debug information

  }//end-read()

  /* this function takes care of the write operation */
  void write(int addr){
    int ndxPD= getPDindex(addr);
    int ndxPT= getPTindex(addr);
    int pgOffset= getPageOffset(addr);
    
    struct entry* pdEntry= &pdbr->entries[ndxPD];//TRICKY here
    
    stat.numCycle+=MEM_COST;//INCREASE COST_________reading PD
    if(!pdEntry->valid){// if not valid
      //PT page fault
      if(DEV_DEBUG)printf("PT page fault\n");
      
      int freePageFrameNdx=alloc_page_frame();

      if(pdEntry->on_disk){
	if(DEV_DEBUG)printf("PT page on disk, swapping in..\n");
	swapIn(pdEntry->disk_addr, freePageFrameNdx);
      } else {
	if(DEV_DEBUG)printf("PT page not on disk, create new PT page \n");
	new_page(freePageFrameNdx);
	pdEntry->frame_addr = page_frames[freePageFrameNdx];
	stat.numPDEntry++;
      }

      stat.numPT++;
      stat.numPTcurrent++;
      if(stat.numPTcurrent>stat.numPTMax) stat.numPTMax=stat.numPTcurrent;
      
      pdEntry->valid= true;
    }// end if not valid

    else {
      if(DEV_DEBUG)printf("PT page found\n");
    }

    struct page* PT= pdEntry->frame_addr;
    struct entry* PTEntry = &PT->entries[ndxPT];//

    stat.numCycle+=MEM_COST;// INCREASE COST___________reading PT
    if(!PTEntry->valid){
      //user page fault
      if(DEV_DEBUG)printf("User page fault\n");

      int freePageFrameNdx=alloc_page_frame();
      if(PTEntry->on_disk){
	if(DEV_DEBUG)printf("user page on disk, swapping in.. \n");
	swapIn(PTEntry->disk_addr, freePageFrameNdx);
      } else{
	if(DEV_DEBUG)printf("user page not on disk: create new user page \n");
	new_page(freePageFrameNdx);
	PTEntry->frame_addr=page_frames[freePageFrameNdx];
      }

      stat.numPageTotal++;
      stat.numPageCurrent++;
      if(stat.numPageCurrent>stat.numPageMax) stat.numPageMax=stat.numPageCurrent;  

      PTEntry->valid = true;
      pdEntry->valid = true;
    } else{
      if(DEV_DEBUG) printf("user page found\n");
    }

    // accessing user page
    struct page* userPage = PTEntry->frame_addr;
    stat.numCycle+=MEM_COST;//INCREASE COST_________reading user page


    PTEntry->dirty =true;
    pdEntry->dirty = true;
    stat.numWrite++;

    if(_DEBUG) logDebugInfo();//take notes of debug information
  }//end_write()


};//end class




/* The driver creates and drives the cache. It scans through the input
 * and extract the r/w instructions to drive the cache, create statistics
 * It reports errors if input file is not valid or contains errors  */
class driver{
  char* fileString;//to store filename passed with command
public:
  driver(char* arg){
    fileString = arg;
  }

 void process(){
   //reopen and redirect stdin to the file
   FILE* inFile = freopen(fileString,"r",stdin);

   /*to read from stdin without redirecting, just remove the line above
    * and use 'stdin' to replace the 'inFile' in the line below
    * I redirected to the file since I am more used to this way */
   if(inFile==NULL)printf("INVALID FILE, TRY AGAIN! \n \n");
    else{
      printf("INPUT FILE SUCCESSFULLY LOADED \n");
      vmmsim* myVmm = new vmmsim();

      while(true){
	char temp[2]; //to store r/w indicator
	fscanf(stdin,"%s",temp);//scan them into temp[]

	if(!strcmp(temp,"-p")){
	  char num[20];
	  //printf("found p!\n");
	  fscanf(stdin,"%s",num);
	  // printf("num is %s\n",num);
	  int it=0, N=0;
	  while(num[it]!='\0'){
	    N=N*10+(num[it]-'0');
	    it++;
	  }
	  //printf("num in int is %d\n",N);
	  N_frames=N;

	  if(N_frames<MIN_NUM_FRAMES){
	    fprintf(stderr,"Too few page frames!\n");
	    exit(1);
	  }
	  continue;
	}
	if(!strcmp(temp,"-v")){
	  _VERSION=true;
	  temp[0]=' '; //the temp need to be cleared, otherwise infinite loop!
	  continue;
	} 
	if(!strcmp(temp,"-d")){
	  _DEBUG=true;
	  //printf("DEBUG>>\n");
	  temp[0]=' ';
	  continue;
	}
	if(!strcmp(temp,"-t")){
	  _TRACE = true;
	  //printf("TRACE>>\n");
	  temp[0]=' ';
	  continue;
	}
	char temp2[10];//to store address starting with 0x..
	fscanf(stdin,"%s",temp2);
	//printf("size of temp: %d\n",sizeof(temp));
	if(feof(stdin)) break;
	/*kind of 'hack' here --  I extracted the third
	 * char through the eighth from the address, which 
	 * is the real address, the head "0x" is dumped... */
	if(!strcmp(temp,"r")||!strcmp(temp,"R")){
	  if(_TRACE)printf("reading from address: %s\n",temp2);
	  myVmm->read(hexToInt(&temp2[2]));
	}
	else if(!strcmp(temp,"w")||!strcmp(temp,"W")){
	  if(_TRACE)printf("writing to address: %s\n",temp2);
	  myVmm->write(hexToInt(&temp2[2]));
	}
	//report strange character in input if found
	//-t -v -d are skipped before,so don't need to care about them here
	else {
	  printf("STRANGE CHAR! CHECK YOUR INPUT!!!!!!!!!\n");
	  return;
	}
	      
      }//end-while-loop

      fclose(stdin);//close the stdin stream
      if(_VERSION)printf("[[- BUILD VERSION: 1.4 -]]\n");
      if(_DEBUG)printf("[[- DEBUG ACTIVATED -]]\n");
      if(_TRACE)printf("[[- TRACE ACTIVATED -]]\n");
      printStat();
      }//end-else

   /* following block prints out debug info in LIFO order!!  */
   if(_DEBUG){
     printf("---- DEBUG INFORMATION IN LIFO ORDER -----\n");
     while(!debugInfo.empty()){
       if(_DEBUG)cout<<debugInfo.top();
       debugInfo.pop();
     }
     printf("------END OF DEBUG INFO------\n");
   }
   
 }//end-function

};

int main(int argc, char* argv[]){
  //set up Version, Trace, Debug if entered from keyboard
  for(int n=1;n<argc;++n){
    if(strcmp(argv[n],"-d")==0) _DEBUG = true;
    if(strcmp(argv[n],"-v")==0) _VERSION = true;
    if(strcmp(argv[n],"-t")==0) _TRACE = true;
  }//end-for

  /*feed the input file(last arg) into the driver for initialization*/
  driver* myDriver = new driver(argv[argc-1]); 
  myDriver->process();
}
