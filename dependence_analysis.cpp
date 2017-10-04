#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"					//header files
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Value.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Constants.h"
#include "llvm/Analysis/IVUsers.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"


using namespace llvm;

namespace
{

        struct P : public FunctionPass
        {
                static char ID;
                P () : FunctionPass(ID){}

                bool runOnFunction (Function &F) override
                {
			auto &LALA = getAnalysis<LoopAccessLegacyAnalysis>();
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();//getting the information of the loop in LoopInfo *
			DependenceInfo &DI = getAnalysis<DependenceAnalysisWrapperPass>().getDI();	
			MemoryDependenceResults &MDA = getAnalysis<MemoryDependenceWrapperPass>().getMemDep();

			enum DepType {
      			Clobber = 0,
      			Def,
      			NonFuncLocal,
      			Unknown
    			};

   			static const char *const DepTypeStr[];
			typedef PointerIntPair<const Instruction *, 2, DepType> InstTypePair;
    			typedef std::pair<InstTypePair, const BasicBlock *> Dep;
			typedef SmallSetVector<Dep, 4> DepSet;
    			typedef DenseMap<const Instruction *, DepSet> DepSetMap;
    			DepSetMap Deps;

		errs () << "\n\n\n*******************************PRINTING ANALYSIS USING MEMORYDEPENDENCEANALYSIS.H FILE*******************************\n\n\n";

  			for (auto &I : instructions(F)) 
			{

		    		Instruction *Inst = &I;

		    		if (!Inst->mayReadFromMemory() && !Inst->mayWriteToMemory()) {continue;}

		    		MemDepResult Res = MDA.getDependency(Inst);
		    		
				if (!Res.isNonLocal()) 
				{
		      			Deps[Inst].insert(std::make_pair(getInstTypePair(Res),
						       static_cast<BasicBlock *>(nullptr)));
		    		} 
				else if (auto CS = CallSite(Inst)) 
				{
		      			const MemoryDependenceResults::NonLocalDepInfo &NLDI =
					MDA.getNonLocalCallDependency(CS);

		      			DepSet &InstDeps = Deps[Inst];
		      			for (const NonLocalDepEntry &I : NLDI) 
					{
					const MemDepResult &Res = I.getResult();
					InstDeps.insert(std::make_pair(getInstTypePair(Res), I.getBB()));
		      			}
		    		} 	
				else 
				{
		      			SmallVector<NonLocalDepResult, 4> NLDI;
		      			assert( (isa<LoadInst>(Inst) || isa<StoreInst>(Inst) || isa<VAArgInst>(Inst)) && "Unknown memory instruction!");
		      			MDA.getNonLocalPointerDependency(Inst, NLDI);

		      			DepSet &InstDeps = Deps[Inst];
		      			for (const NonLocalDepResult &I : NLDI) 
					{
					const MemDepResult &Res = I.getResult();
					InstDeps.insert(std::make_pair(getInstTypePair(Res), I.getBB()));
		      			}
		    		}
	
  				for (const auto &I : instructions(*F)) 
				{
    					const Instruction *Inst = &I;

    					DepSetMap::const_iterator DI = Deps.find(Inst);
    					if (DI == Deps.end()) {continue;}

    					const DepSet &InstDeps = DI->second;

    					for (const auto &I : InstDeps) 
					{
      						const Instruction *DepInst = I.first.getPointer();
      						DepType type = I.first.getInt();
      						const BasicBlock *DepBB = I.second;

      						OS << "    ";
      						OS << DepTypeStr[type];
      					
						if (DepBB) 
						{
        						OS << " in block ";
        						DepBB->printAsOperand(O, /*PrintType=*/false, M);
      						}
      						if (DepInst) 
						{
        						OS << " from: ";
        						DepInst->print(OS);
      						}
      					errs() << "\n";
    					}	

    					errs() << "\n\n";
  				}

		  }

			
		errs () << "\n\n\n*******************************PRINTING ANALYSIS USING LOOPACCESSANALYSIS.H FILE*******************************\n\n\n";
	
			for (Loop* L:LI)
			{
			auto &LAI= LALA.getInfo(L);
			const MemoryDepChecker *DepChecker = &LAI.getDepChecker();
			
			MemoryDepChecker *MDC = const_cast<MemoryDepChecker *>(DepChecker);
			
			if (auto *Dependences = DepChecker->getDependences()) 
			{
    				for (auto &Dep : *Dependences) 
				{
				errs () << "Dependence Name is -> ";
				errs () << *Dep.DepName << "\n";

				errs () << "Source of dependence is ->";
				errs () << *Dep.getSource(LAI) << "\n";

				errs () << "Destination for dependence is ->";
				errs () << *Dep.getDestination(LAI) << "\n";

				if (Dep.isSafeForVectorization(Dep.Type)) {"Depndence safe for vectorization\n";}
				else {"Depndence safe for vectorization\n";}    			

				if (Dep.isForward()){errs () << "Dependence is forward\n";}
				else if (Dep.isBackward()){errs () << "Dependence is backward\n";}
				else if (Dep.isPossiblyBackward()){errs () << "Dependence is possibly backward\n";}
		
				}

  			}
			else
    			errs()  << "Too many dependences, not recorded\n";

			if (MDC->isSafeForVectorization()) {errs () << "No memory dependence was encountered that would inhibit vectorization\n";}
			else {errs () << "Unsafe for vectorization\n";}

			//MemoryDepChecker *non_const_MDC = const_cast<MemoryDepChecker *>(DepChecker);
			
			errs () << "The maximum number of bytes of a vector register we can vectorize  the accesses safely with = " << 
			MDC->getMaxSafeDepDistBytes() << "\n";

			if (MDC->shouldRetryWithRuntimeCheck()) {errs () << ("In same cases when the dependency check fails we can still \
			vectorize the loop with a dynamic array access check\n");}		
			}

		errs () << "\n\n\n*******************************PRINTING ANALYSIS USING DEPENDECEANALYSIS.H FILE*******************************\n\n\n";

  			
			for (Loop *L: LI)
			{
			SmallVector<Value *, 16>  MemInstr;

  				// For each block.
  			Loop::block_iterator b1,b2;
			b1=L->block_begin();
			b2=L->block_end();
	
			for (;b1!=b2;b1++) 
			{
    			
				BasicBlock::iterator i1,i2;
				i1=(*b1)->begin();
				i2=(*b1)->end();
	
    				for (;i1!=i2;i1++) 
				{
					if (!isa<Instruction>(i1))
						return false;
					if (dyn_cast<LoadInst>(i1)) 
					{
					MemInstr.push_back(&*i1);
					} 
					else if (dyn_cast<StoreInst>(i1)) 
					{
					MemInstr.push_back(&*i1);
					}
   				}	
  			}

			SmallVector<Value *, 16>::iterator I, IE, J, JE;

  			for (I = MemInstr.begin(), IE = MemInstr.end(); I != IE; ++I) 
			{
    				for (J = I, JE = MemInstr.end(); J != JE; ++J) 
				{
					std::vector<char> Dep;
	      
					Instruction *Src = cast<Instruction>(*I);
					Instruction *Dst = cast<Instruction>(*J);
				
					if (Src == Dst)
						continue;
	      
					// Ignore Input dependencies.
	      
					if (auto D = DI.depends(Src, Dst, true)) 
					{
					
					errs () << "Source instruction is --> " << *D->getSrc() << "\n";
					errs () << "Destination instruction is --> " << *D->getDst() << "\n";				
			
					if (D->isOrdered()) {errs() << "The dependence is Ordered and of type --> ";}
					{
						if (D->isOutput()) {errs() << " Output dependence\n";}
						if (D->isFlow()) {errs() << " Flow/True dependence\n";}
						if (D->isAnti()) {errs() << " Anti dependence\n";}
					}
					if(D->isUnordered()) {errs() << "The dependence is Unordered dependence and of type -->";}
					{
						if (D->isInput()) {errs() << " Input dependence\n";}
					}

					errs () << "Number of common loops surrounding the source and destination of the dependence = " << D->getLevels() << "\n";
		
					if (D->isLoopIndependent()){errs () << "Dependence is loop independent\n";}
					else {errs () << "Dependence is loop dependent\n";}

					if (D->isConfused()) {errs () << "Dependence is confused and compiler wold make worst case assumption\n";}
					if (D->isConsistent()) {errs () << "Dependence is consistant\n";}

					if (D->getLevels()>0)
					{
						for (unsigned i=1;i<=D->getLevels();i++)	
						{
						errs () << 		"--for level = " << i << " --\n";
         					
						const SCEV *Distance = D->getDistance(i);
          					const SCEVConstant *SCEVConst = dyn_cast_or_null<SCEVConstant>(Distance);
          
						if (SCEVConst!=NULL) 
						{
            						const ConstantInt *CI = SCEVConst->getValue();
            						if (CI->isNegative())
              							errs () << "Direction of the dependency is '<'" << "\n";

            						else if (!CI->isNegative())
              							errs () << "Direction of the dependency is '>'" << "\n";

            						else
              							errs () << "Direction of the dependency is '='" << "\n";
          					} 
						else if (D->isScalar(i)) 
						{
            						errs () << "Directional dependency is Scalar type \n" << "\n";
          					} 
						else 
						{
            						unsigned Dir = D->getDirection(i);
            						if (Dir == Dependence::DVEntry::LT || Dir == Dependence::DVEntry::LE)
              							errs () << "Direction of the dependency is '<'" << "\n";
            						else if (Dir == Dependence::DVEntry::GT || Dir == Dependence::DVEntry::GE)
              							errs () << "Direction of the dependency is '>'" << "\n";
            						else if (Dir == Dependence::DVEntry::EQ)
              							errs () << "Direction of the dependency is '='" << "\n";		
						        else
              							errs () << "Directional dependency is unknown \n" << "\n";

						}


						if (D->isPeelFirst(i)){errs () << "Peeling the first iteration from this loop will break this dependence\n";}
						if (D->isPeelLast(i)){errs () << "Peeling the last iteration from this loop will break this dependence\n";}	
						
						} 
					     }	
					}
				 }
			}

		}

                return false;
          }	
	  void getAnalysisUsage(AnalysisUsage &AU) const override 
	  {
    	 	AU.setPreservesAll();					      //marking as analysis pass and pre run of the other pass
	  	AU.addRequired<LoopInfoWrapperPass>();
		AU.addRequired<LoopAccessLegacyAnalysis>();
		AU.addRequired<DependenceAnalysisWrapperPass>();
		AU.addRequired<MemoryDependenceWrapperPass>();
	  }


	};
}

char P::ID=0;
static RegisterPass <P> X("P","P");
