/* HW4 CS538 Vmm Sim Implementation, Fall 2011, Xiaolong Cheng */

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


// by default, debug, trace and version command are all disabled
bool _DEBUG = false;
bool _TRACE = false;
bool _VERSION = false;

// default frame number is 10
int N_frames =10;

//stack<string> debugInfo; // LIFO for debug information

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
  int numPT;
  int numPTMax;
  int numPageTotal;
  int numPageMax;
  int numFrame;
} stat ={0,0,0,0,0,0,0,0,0,0,0,0,0,0};

void printStat(){

  printf("--------------STATISTICS---------------\n");
  printf("Access: %d\n Reads: %d\n Writes: %d\n Cycles: %d\n Cycles Without VMM :%d\n Swap ins: %d\n Swap outs: %d\n Pure Replacements: %d\n PD entries used: %d\n PT total: %d\n PT max: %d\n user pages total: %d\n user pages max: %d\n Physical page frames: %d\n",stat.numAccess, stat.numRead, stat.numWrite, stat.numCycle, stat.numCyclesWithoutVmm, stat.numSwapIn, stat.numSwapOut, stat.numReplacement, stat.numPDEntry, stat.numPT, stat.numPTMax, stat.numPageTotal, stat.numPageMax, stat.numFrame);
  printf("-----------------END-----------------\n");
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
      if(_DEBUG)printf("returning frame index %d\n",i);
      return i;
    }
  }
  fprintf(stderr,"page frame not found!\n");
  exit(1);
}

/* create a new page in page frames with index idx */
void new_page(int idx){
  page_frames[idx]=(page*)calloc(1,sizeof(struct page));
  if(_DEBUG)printf("new page at page_frames[%d]\n",idx);
  if(!page_frames[idx]){
    fprintf(stderr,"not enough memory for newing a page!\n");
    exit(1);
  }
}


/* allocate an empty page frame and return its index */
int alloc_page_frame(){
  int j,result;

  //check if free page frame available
  for(int i=0; i<N_frames;++i){
    if(page_frames[i]==NULL){
      if(_DEBUG)printf("found unused page frame %d\n",i);
      return i;
    }
  }


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

    //TODO
    //more initialization...
    
  }

  /* to allocate new disk space */
  struct diskblock* allocDiskBlock(){
    struct diskblock* dblk= (diskblock*)malloc(sizeof(struct diskblock));
    if(!dblk){
      fprintf(stderr,"allocDiskBlock: Not enough memory!\n");
      exit(1);
    }
    if(_DEBUG)printf("allocated new disk block %p \n",dblk);
    return dblk;
  }

  /*swap in a page from disk to given frame index */
  void swapIn(struct diskblock* disk, int frameIdx){
    if(_DEBUG)printf("Swap in page %d from disk %p \n",frameIdx,disk);
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
    if(_DEBUG) printf("Swap out %p to %p \n",frame,dblk);
    stat.numSwapOut++;
  }


  void read(int addr){
    // printf("int addr is %d\n",addr);
  }

  void write(int addr){

  }


};




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
	  printf("STRANGE CHAR! CHECK YOUR INPUT!!!!!!!!!!!!!!!!!\n");
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
  /* if(_DEBUG)printf("BELOW IS DEBUG INFORMATION IN LIFO ORDER\n");
   while(!debugInfo.empty()){
     if(_DEBUG)cout<<debugInfo.top();
     debugInfo.pop();
   }*/
   
 }//end-function

};

int main(int argc, char* argv[]){
  //set up Version, Trace, Debug if entered from keyboard
  for(int n=1;n<argc;++n){
    if(strcmp(argv[n],"-d")==0) _DEBUG = true;
    if(strcmp(argv[n],"-v")==0) _VERSION = true;
    if(strcmp(argv[n],"-t")==0) _TRACE = true;
  }//end-for

  if(N_frames<MIN_NUM_FRAMES){
    fprintf(stderr,"Too few page frames!\n");
    exit(1);
  }


  /*feed the input file(last arg) into the driver for initialization*/
  driver* myDriver = new driver(argv[argc-1]); 
  myDriver->process();
}
