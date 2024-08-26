#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include <fstream>
#include "llvm/IR/LegacyPassManager.h"
#include <bits/stdc++.h>

// Author : Soumya Banerjee     (CS22MTECH12011)
// How to run : /path/to/opt -load /path/to/lib/file.so -passname -enable-new-pm=0 ../path/to/assign/file.ll > output.ll => will print the output IR on the screen / redirect to any file ,
//                 for all separate input.ll files, in a common directory you can use the sample_runme.sh 
//  NOTE : I am not printing the --> BOTTOM thing after each call site, since we are assuming void type function calls, hence int x = foo(a,b), x will always be BOTTOM, hence not printing separately


using namespace llvm;
using namespace std;


namespace {
struct cons_eval : public ModulePass {
    static char ID;
    // std::map<int, std::map<std::string, std::string>> globalVariableMap;
        map<string,map<int, std::map<std::string, std::string>>>globalVariableMap;
        
        std::map<std::string, pair<string,int>> globalinstructionLineMap;
        set<string>Bottom;  // to not recalculate Eval for functions whose params are known to be botoom always
       
        map<string,map<int,vector<string>>>jumpFunction;    // function name -> lineNumbers -> {calledFunctionName, actualParams[0], actualParams[1],...}
        map<string,vector<string>>formalParams;
        set<string>allFunctions;
        // map<string, vector<vector<string>>>jumpFunction;   // function A is being called by say B, C, we want to know the actual params passed by B and C, take meet and do const prop on A
        map<string, map<string,vector<int>>>returnJumpFunction; // what values function B is returning when called from different call sites, but context insensitive, so doesn't matter
        cons_eval() : ModulePass(ID) {}


    
        bool containsOnlyNumeric(const std::string &str) {
            for (char c : str) {
                if (!isdigit(c)) {
                    return false;
                }
            }
            return true;
        }

        map<int,map<string,string>> Eval (Function &F, vector<string> Params){
            std::map<int, std::map<std::string, std::string>> variableMap;
            std::map<std::string, std::string> latestValuesMap;
            std::map<std::string, std::string> globallatestValuesMap;
            // std::map<std::string, std::map<std::string, std::string>> basicBlockVariableMap; // Map for basic blocks
            std::map<BasicBlock *, std::map<std::string, std::string>> basicBlockVariableMap;
            std::map<std::string, int> instructionLineMap;
            map<int,set<BasicBlock *>>levelsToBB;
            map<BasicBlock *, int>BBtoLevels;

            int lineNum = 0;
            for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I, ++lineNum){
                Instruction &Inst = *I;
                std::string instStr;
                raw_string_ostream instStream(instStr);
                Inst.print(instStream);
                instructionLineMap[instStream.str()] = lineNum;
            }


            for (BasicBlock &BB : F) {
                basicBlockVariableMap[&BB] = std::map<std::string, std::string>(); // Initialize each BasicBlock's map as empty
            }

            std::set<BasicBlock *> visited; // Set to keep track of visited basic blocks
            std::queue<BasicBlock *> worklist; 

            BasicBlock *entry = &F.getEntryBlock();
            bool change = false;
            int hardstop = 50;
            int time = 0;

            worklist.push(entry);
            visited.insert(entry);

            int levels = 0;
            // BBtoLevels[entry]=levels;
            set<BasicBlock *>forsets,dosets,whilesets,forendsets,doendsets,whileendsets;
            // sort of preprocessing to help load proper values for special cases
            while(!worklist.empty()){
                int count=worklist.size();
                while(count--){
                    BasicBlock *CurrBB = worklist.front();
                    worklist.pop();
                    BBtoLevels[CurrBB]=levels;
                    levelsToBB[levels].insert(CurrBB); 
                    // Ik, ik some string matching, but < 1% of entire program (handles special case of some loops)
                    if((CurrBB->getName().str().find("for.body") != std::string::npos)){
                        forsets.insert(CurrBB);
                    }
                    else if((CurrBB->getName().str().find("while.body") != std::string::npos)){
                        whilesets.insert(CurrBB);
                    }
                    else if((CurrBB->getName().str().find("do.body") != std::string::npos)){
                        dosets.insert(CurrBB);
                    }
                    else if((CurrBB->getName().str().find("for.end") != std::string::npos)){
                        forendsets.insert(CurrBB);
                    }
                    else if((CurrBB->getName().str().find("while.end") != std::string::npos)){
                        whileendsets.insert(CurrBB);
                    }
                    else if((CurrBB->getName().str().find("do.end") != std::string::npos)){
                        doendsets.insert(CurrBB);
                    }
                    for (BasicBlock *SuccBB : successors(CurrBB)) {
                        if (visited.find(SuccBB)==visited.end()) {
                            worklist.push(SuccBB);
                            // Visited[SuccBB] = true;
                            visited.insert(SuccBB);
                        }
                    }
                }
                levels++;
            }
            visited.clear();

            // some more preprocessing
            if(!forendsets.empty()){
                for (BasicBlock *endBB : forendsets) {
                    if(forsets.empty())
                        break;
                    BasicBlock *bodyBB = *(forsets.begin()); // Get the first element

                    // Assuming forsets is non-empty
                    int level = BBtoLevels[endBB];
                    levelsToBB[level].erase(endBB);
                    BBtoLevels[endBB] = BBtoLevels[bodyBB] + 1;
                    levelsToBB[BBtoLevels[bodyBB] + 1].insert(endBB);
                    forsets.erase(forsets.begin()); // Delete the first element
                }
            }

            if(!whileendsets.empty()){
                for (BasicBlock *endBB : whileendsets) {
                    if(whilesets.empty())
                        break;
                    BasicBlock *bodyBB = *(whilesets.begin()); // Get the first element

                    // Assuming forsets is non-empty
                    int level = BBtoLevels[endBB];
                    levelsToBB[level].erase(endBB);
                    BBtoLevels[endBB] = BBtoLevels[bodyBB] + 1;
                    levelsToBB[BBtoLevels[bodyBB] + 1].insert(endBB);
                    whilesets.erase(whilesets.begin()); // Delete the first element
                }
            }

            if(!doendsets.empty()){
                for (BasicBlock *endBB : doendsets) {
                    if(dosets.empty())
                        break;
                    BasicBlock *bodyBB = *(dosets.begin()); // Get the first element

                    // Assuming forsets is non-empty
                    int level = BBtoLevels[endBB];
                    levelsToBB[level].erase(endBB);
                    BBtoLevels[endBB] = BBtoLevels[bodyBB] + 1;
                    levelsToBB[BBtoLevels[bodyBB] + 1].insert(endBB);
                    dosets.erase(dosets.begin()); // Delete the first element
                }
            }

            worklist.push(entry);
            visited.insert(entry);

            while(((!worklist.empty() || change == true)) && (hardstop--)){
                if(change==true && worklist.empty()){
                    // outs () <<"occuring time : " << time << "\n";
                    time++;
                    worklist.push(entry);
                    visited.clear();
                    visited.insert(entry);
                }
                change=false;
                BasicBlock *CurrBB = worklist.front();
                worklist.pop();
                // outs () << "printing queue front block's name : " << CurrBB->getName() << "\n";

                set<string>firstAccess;
                set<BasicBlock *> nonEmptyPredecessors;
                for (BasicBlock *PredBB : predecessors(CurrBB)) {
                    if (basicBlockVariableMap.find(PredBB) != basicBlockVariableMap.end()) {
                        // outs () << "entering here !! " << "\n";
                        nonEmptyPredecessors.insert(PredBB);
                    }
                }

                latestValuesMap.clear();
                firstAccess.clear();
                int pindex = 0;
                set<string>allocas;
                // if(nonEmptyPredecessors.empty()){

                    for ( Instruction &I : *CurrBB) {
                        auto inst = &I;
                        std::string instStr;
                        raw_string_ostream instStream(instStr);
                        I.print(instStream);
                        instStream.flush();

                        int lineNum = instructionLineMap[instStr];
                        // outs () << instStr <<":"<<lineNum <<"\n";
                        
                        // ALLOCA INST
                        if (auto *allocaInst = dyn_cast<AllocaInst>(inst)) {
                            string varName = allocaInst->getName().str();
                            string extractedName="";
                            // handing values coming from parameters
                            if(allocaInst->getName().str().find("addr")!=string::npos && Params.size()>0){
                                size_t dotPos = varName.find('.');
                                
                                if (dotPos != std::string::npos) {
                                    extractedName = varName.substr(0, dotPos);
                                    // outs () << "extracted name here : "<< extractedName<< "\n";
                                    allocas.insert(extractedName);
                                }
                                
                                variableMap[lineNum][allocaInst->getName().str()] = "TOP";
                                latestValuesMap[allocaInst->getName().str()] = "TOP";
                                globallatestValuesMap[allocaInst->getName().str()] = "TOP";

                                // outs ()<< "Value of Params[pinex ] = "<< Params[pindex] << "\n";
                                variableMap[lineNum][extractedName] = Params[pindex];
                                latestValuesMap[extractedName] = Params[pindex];
                                globallatestValuesMap[extractedName] = Params[pindex];
                                pindex++;
                                // pindex++;
                            }
                            else if(allocas.count(varName)){
                                // outs ()<< "Value of Params[pinex ] = "<< Params[pindex] << "\n";
                                variableMap[lineNum][allocaInst->getName().str()] = Params[pindex];
                                latestValuesMap[allocaInst->getName().str()] = Params[pindex];
                                globallatestValuesMap[allocaInst->getName().str()] = Params[pindex];
                                pindex++;
                            }
                            else{
                                variableMap[lineNum][allocaInst->getName().str()] = "TOP";
                                latestValuesMap[allocaInst->getName().str()] = "TOP";
                                globallatestValuesMap[allocaInst->getName().str()] = "TOP";
                            }

                            // do we need to add the x of x.addr to firstAccess here as well ?
                            
                            if(firstAccess.find(allocaInst->getName().str())==firstAccess.end()){
                                firstAccess.insert(allocaInst->getName().str());
                                if(varName.find("addr")!=string::npos && extractedName!= ""){
                                    firstAccess.insert(extractedName);
                                }
                            }
                        } 
                        // STORE INST
                        else if(auto *storeInst = dyn_cast<StoreInst>(inst)){
                            Value *value = storeInst->getValueOperand();
                            //// outs () << "printing value here : "<< *value << "\n";
                            if (auto *constant = dyn_cast<ConstantInt>(value)) {
                                variableMap[lineNum][storeInst->getPointerOperand()->getName().str()] = std::to_string(constant->getSExtValue());
                                //// outs () << "std::to_string(constant->getSExtValue() = " << std::to_string(constant->getSExtValue()) << "\n";
                                latestValuesMap[storeInst->getPointerOperand()->getName().str()] = std::to_string(constant->getSExtValue());
                                globallatestValuesMap[storeInst->getPointerOperand()->getName().str()] = to_string(constant->getSExtValue());
                                if(firstAccess.find(storeInst->getPointerOperand()->getName().str())==firstAccess.end()){
                                    firstAccess.insert(storeInst->getPointerOperand()->getName().str());
                                }
                            } else {
                                
                                std::string instStr;
                                raw_string_ostream instStream(instStr);
                                inst->print(instStream);
                                instStream.flush();

                                size_t pos1 = instStr.find('%');
                                size_t pos2 = instStr.find(',', pos1);
                                size_t pos3 = instStr.find('%', pos2);
                                size_t pos4 = instStr.find(',', pos3);

                                if (pos1 != std::string::npos && pos2 != std::string::npos &&
                                    pos3 != std::string::npos && pos4 != std::string::npos) {
                                    // Extract the source variable name (e.g., %add)
                                    std::string sourceVar = instStr.substr(pos1, pos2 - pos1);
                                    ////// outs () << "original sourceVAr : " << sourceVar << "\n";

                                    // Extract the destination variable name (e.g., %c)
                                    std::string destVar = instStr.substr(pos3, pos4 - pos3);

                                    ////// outs () << "original destination var : " << destVar << "\n";

                                    // Retrieve the value of the source variable from latestValuesMap
                                    string sourceValue;
                                    if(latestValuesMap.count(sourceVar.substr(1))==0){
                                        sourceValue = (globallatestValuesMap.count(sourceVar.substr(1)))?globallatestValuesMap[sourceVar.substr(1)]:"BOTTOM";
                                    }
                                    else
                                        sourceValue = latestValuesMap[sourceVar.substr(1)];

                                    // Update the latestValuesMap of the destination variable
                                    latestValuesMap[destVar.substr(1)] = sourceValue;
                                    globallatestValuesMap[destVar.substr(1)] = sourceValue;

                                    // Update the variableMap with the values
                                    variableMap[lineNum][sourceVar.substr(1)] = sourceValue;
                                    variableMap[lineNum][destVar.substr(1)] = sourceValue;
                                    if(firstAccess.find(destVar.substr(1))==firstAccess.end()){
                                        firstAccess.insert(destVar.substr(1));
                                    }
                                }
                                else{
                                    // outs () << "Store instruction not proper here " <<"\n";
                                }
                            }
                        }
                        // LOAD INST
                        else if(auto *loadInst = dyn_cast<LoadInst>(inst)){
                            std::string variableName = loadInst->getPointerOperand()->getName().str();
                            // outs () << "variable name inside loadInst : "<< variableName << "\n";
                            std:: string lhs_var;
                            std::string instructionString;
                            raw_string_ostream instructionStream(instructionString);
                            loadInst->print(instructionStream);
                            instructionString = instructionStream.str();
                            // ////// outs () << "the instruction string : "<<instructionString <<"\n";
                            size_t equalPos = instructionString.find("=");
                            if (equalPos != std::string::npos) {
                                lhs_var = instructionString.substr(0, equalPos);                            // HANDLE THIS CASE REMEMBER
                                lhs_var.erase(std::remove_if(lhs_var.begin(), lhs_var.end(), ::isspace), lhs_var.end());
                                lhs_var = lhs_var.substr(1);
                            }
                            // //// outs () << "variable name inside loadInst to the left : "<< lhs_var << "\n";
                            std::string variableValue="";
                            
                            if(firstAccess.find(variableName)==firstAccess.end() && !nonEmptyPredecessors.empty()){
                                // outs () << "is it even entering here ? " <<"\n";
                                // incase of predecessors, we will take the meet here
                                firstAccess.insert(variableName);
                                // this line won't be there then if predecssor values are being taken
                                // std::string variableValue = latestValuesMap[variableName];
                                // MAIN PREDECESSOR LOGIC 
                                
                                bool allSameValue = true;
                                // outs () << "printing list of predecessors : " << "\n";
                                // CHECK if *Pred or just Pred
                                for (BasicBlock *Pred : nonEmptyPredecessors) {
                                    // while (Pred->getName().find("end") != std::string::npos) {
                                    //     Pred = *predecessors(Pred).begin();
                                    // }
                                    // outs () << Pred->getName().str() << " ";
                                    string predVarVal = "";
                                    if(basicBlockVariableMap[Pred].count(variableName)){
                                        // outs () << "working correctly it seems" << "\n";
                                        predVarVal = basicBlockVariableMap[Pred][variableName];
                                    }
                                    ////// outs () << "values of predvarval : " << predVarVal << "\n";
                                    if(predVarVal=="")
                                        continue;
                                    if (variableValue=="") {
                                        variableValue = predVarVal;
                                    } else if (variableValue != predVarVal) {
                                        allSameValue = false;
                                        break;
                                    }
                                }
                                // outs () << "\n";
                                if (allSameValue) {
                                    if(variableValue == ""){
                                        // implement the logic for levels
                                        int level = BBtoLevels[CurrBB];
                                        // outs () << "current level of the basic block : " << level <<"\n";
                                        // level--;
                                        bool foundinlevel = false;
                                        bool innerallSameValue = true;
                                        for(;level>=0;level--){
                                            for(BasicBlock *Pred : levelsToBB[level]){
                                                if(Pred == CurrBB)
                                                    continue;
                                                string predVarVal = "";
                                                // outs () << "predecessor ancestors names : " << Pred->getName().str() << " ";
                                                if(basicBlockVariableMap[Pred].count(variableName)){
                                                    // outs () << "working correctly it seems even inside for ancestor predecessors" << "\n";
                                                    predVarVal = basicBlockVariableMap[Pred][variableName];
                                                }
                                                // outs () << "values of predvarval of ancestors: " << predVarVal << "\n";
                                                if(predVarVal=="")
                                                    continue;
                                                if (variableValue=="") {
                                                    foundinlevel = true;
                                                    variableValue = predVarVal;
                                                } else if (variableValue != predVarVal) {
                                                    innerallSameValue = false;
                                                    break;
                                                }
                                            }
                                            if(foundinlevel)
                                                break;
                                        }
                                        if(foundinlevel && !innerallSameValue)
                                            variableValue = "BOTTOM";
                                        if(!foundinlevel || variableValue == "")
                                            variableValue = (globallatestValuesMap.count(variableName))?globallatestValuesMap[variableName]:"BOTTOM";
                                    }

                                } else {
                                    
                                    variableValue = "BOTTOM";
                                }
                                // latestValuesMap[variableName]=variableMap[lineNum][variableName];
                                // latestValuesMap[lhs_var]=variableMap[lineNum][lhs_var];

                                if ((CurrBB->getName().str().find("body") != std::string::npos) || (CurrBB->getName().str().find("inc") != std::string::npos)){
                                    
                                    variableValue = "BOTTOM";
                                }

                            }
                            else{
                                // outs () << "weirdly coming here ? " << "\n";
                                if(latestValuesMap.count(variableName))
                                    variableValue = latestValuesMap[variableName];
                                else    
                                    variableValue = (globallatestValuesMap.count(variableName))?globallatestValuesMap[variableName]:"BOTTOM";
                            }
                            if (variableValue != "" || variableValue != "TOP" || variableValue != "BOTTOM") {
                                variableMap[lineNum][variableName] = variableValue;
                                variableMap[lineNum][lhs_var] = variableValue;
                                latestValuesMap[lhs_var] = variableValue;
                                latestValuesMap[variableName]=variableValue;
                                globallatestValuesMap[lhs_var]=variableValue;
                                globallatestValuesMap[variableName]=variableValue;
                            } else {
                                variableMap[lineNum][lhs_var] = "BOTTOM";
                                variableMap[lineNum][variableName] = "BOTTOM";
                                latestValuesMap[lhs_var] = "BOTTOM";
                                latestValuesMap[variableName]="BOTTOM";
                                globallatestValuesMap[lhs_var] = "BOTTOM";
                                globallatestValuesMap[variableName]="BOTTOM";

                            }
                        }
                        // BINARY OPERATION INST
                        else if(auto *binaryOp = dyn_cast<BinaryOperator>(inst)){
                            std::string operand1Name = binaryOp->getOperand(0)->getNameOrAsOperand();
                            std::string operand2Name = binaryOp->getOperand(1)->getNameOrAsOperand();
                            // outs () << "operandNames : " << operand1Name << "," << operand2Name << "\n";
                            std::string operand1, operand2;
                            auto flag1=0,flag2=0;

                            // OPERAND 1 CALCULATION
                            if (operand1Name.find('%')!=std::string::npos && latestValuesMap.count(operand1Name.substr(1))) {
                                operand1 = latestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)];
                                flag1=1;
                            } 
                            else if(std::any_of(operand1Name.begin(), operand1Name.end(), ::isalpha) && latestValuesMap.count(operand1Name)){
                                operand1 = latestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand()];
                            }
                            else if(operand1Name.find('%')!=std::string::npos && globallatestValuesMap.count(operand1Name.substr(1))){
                                operand1 = globallatestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)];
                                flag1 = 2;
                            }
                            else if(std::any_of(operand1Name.begin(), operand1Name.end(), ::isalpha) && globallatestValuesMap.count(operand1Name)){
                                operand1 = globallatestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand()];
                            }
                            else {
                                operand1 = (std::string)binaryOp->getOperand(0)->getNameOrAsOperand();
                            }

                            // OPERAND 2 CALCULATION 
                            if (operand2Name.find('%')!=std::string::npos && latestValuesMap.count(operand2Name.substr(1))) {
                                operand2 = latestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)];
                                flag2=1;
                            } 
                            // CHECK LOGIC HERE
                            else if(std::any_of(operand2Name.begin(), operand2Name.end(), ::isalpha) && latestValuesMap.count(operand2Name)){
                                operand2 = latestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand()];
                            }
                            else if(operand2Name.find('%')!=std::string::npos && globallatestValuesMap.count(operand2Name.substr(1))){
                                operand2 = globallatestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)];
                                flag2=2;
                            }
                            else if(std::any_of(operand2Name.begin(), operand2Name.end(), ::isalpha) && globallatestValuesMap.count(operand2Name)){
                                operand2 = globallatestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand()];
                            }
                            else {
                                operand2 = (std::string)binaryOp->getOperand(1)->getNameOrAsOperand();
                            }
                            
                            int resultValue = 0;

                            // outs () << "operand1 = "<<operand1 <<" , operand2 = "<< operand2 << "\n";
                            if(operand1 == "")
                                operand1 = "BOTTOM";
                            if(operand2 == "")
                                operand2 = "BOTTOM";

                            // outs () << "AFTER CHANGE : operand1 = "<<operand1 <<" , operand2 = "<< operand2 << "\n";

                            if(containsOnlyNumeric(operand1) && containsOnlyNumeric(operand2)){
                                    int value1 = std::stoi(operand1);
                                    int value2 = std::stoi(operand2);
                                    switch (binaryOp->getOpcode()) {
                                        case Instruction::Add:
                                            resultValue = value1 + value2;
                                            break;
                                        case Instruction::Sub:
                                            resultValue = value1 - value2;
                                            break;
                                        case Instruction::Mul:
                                            resultValue = value1 * value2;
                                            break;
                                        case Instruction::SDiv:
                                            resultValue = value1 / value2;
                                            break;
                                        case Instruction::SRem:
                                            resultValue = value1 % value2;
                                            break;
                                        case Instruction::Xor:
                                            resultValue = value1 ^ value2;
                                            break;
                                        case Instruction::Or:
                                            resultValue = value1 | value2;
                                            break;
                                        case Instruction::And: // Handle AND operation
                                            resultValue = value1 & value2;
                                            break;
                                        // Add cases for other binary operations as needed
                                        default:
                                            // Unsupported operation, mark as BOTTOM
                                            resultValue = 0; // Or any other appropriate value for BOTTOM
                                            break;
                                    }
                                    // Update the variable map and latestValuesMap with the result value
                                    variableMap[lineNum][binaryOp->getName().str()] = std::to_string(resultValue);
                                    if (flag1 == 1)
                                        variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)] = latestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)];
                                    else if(flag1 == 2)
                                        variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)] = globallatestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)];
                                    if (flag2 == 1)
                                        variableMap[lineNum][(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)] = latestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)];
                                    else if(flag2 == 2)
                                        variableMap[lineNum][(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)] = globallatestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)];
                                    latestValuesMap[binaryOp->getName().str()] = std::to_string(resultValue);
                                    globallatestValuesMap[binaryOp->getName().str()] = std::to_string(resultValue);
                            }
                            else{

                                if((operand1=="BOTTOM"|| operand1=="TOP") && (operand2=="BOTTOM"|| operand2=="TOP")){
                                    variableMap[lineNum][binaryOp->getName().str()] = "BOTTOM";
                                    latestValuesMap[binaryOp->getName().str()] = "BOTTOM";
                                    globallatestValuesMap[binaryOp->getName().str()] = "BOTTOM";
                                    variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)]="BOTTOM";
                                    variableMap[lineNum][(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)]="BOTTOM";
                                }
                                else if(operand1=="BOTTOM"|| operand1=="TOP"){
                                    variableMap[lineNum][binaryOp->getName().str()] = "BOTTOM";
                                    latestValuesMap[binaryOp->getName().str()] = "BOTTOM";
                                    globallatestValuesMap[binaryOp->getName().str()] = "BOTTOM";
                                    variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)]="BOTTOM";
                                    if(operand2Name.find("%")!=string::npos){
                                        if(latestValuesMap.count(operand2Name.substr(1)))
                                            variableMap[lineNum][(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)]=latestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)];
                                        else if(globallatestValuesMap.count(operand2Name.substr(1)))
                                            variableMap[lineNum][(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)]=globallatestValuesMap[(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)];
                                        else
                                            variableMap[lineNum][(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)]="BOTTOM";

                                    }

                                }
                                else if(operand2=="BOTTOM" || operand2=="TOP"){
                                    variableMap[lineNum][binaryOp->getName().str()] = "BOTTOM";
                                    latestValuesMap[binaryOp->getName().str()] = "BOTTOM";
                                    // variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)]=latestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)];
                                    if(operand1Name.find("%")!=string::npos){
                                        if(latestValuesMap.count(operand1Name.substr(1)))
                                            variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)]=latestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)];
                                        else if(globallatestValuesMap.count(operand1Name.substr(1)))
                                            variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)]=globallatestValuesMap[(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)];
                                        else
                                            variableMap[lineNum][(std::string)binaryOp->getOperand(0)->getNameOrAsOperand().substr(1)]="BOTTOM";
                                    }
                                    variableMap[lineNum][(std::string)binaryOp->getOperand(1)->getNameOrAsOperand().substr(1)]="BOTTOM";
                                }

                            }                            
                            if(firstAccess.find(binaryOp->getName().str())==firstAccess.end()){
                                firstAccess.insert(binaryOp->getName().str());
                            }
                        }
                        // ICMP INST
                        else if(auto *icmpInst = dyn_cast<ICmpInst>(inst)){
                            std::string operand1Name = icmpInst->getOperand(0)->getNameOrAsOperand();
                            std::string operand2Name = icmpInst->getOperand(1)->getNameOrAsOperand();
                            ////// outs () << "operand1Naem : " << operand1Name << "\n";

                            std::string operand1, operand2;
                            auto flag1=0,flag2=0;
                            // OPERAND 1 CALCULATION 
                            if (operand1Name.find('%')!=std::string::npos && latestValuesMap.count(operand1Name.substr(1))) {
                                operand1 = latestValuesMap[(std::string)icmpInst->getOperand(0)->getNameOrAsOperand().substr(1)];
                                flag1=1;
                            } 
                            else if(std::any_of(operand1Name.begin(), operand1Name.end(), ::isalpha) && latestValuesMap.count(operand1Name.substr(1))){
                                operand1 = latestValuesMap[(std::string)icmpInst->getOperand(0)->getNameOrAsOperand()];
                            }
                            else if(operand1Name.find('%')!=std::string::npos && globallatestValuesMap.count(operand1Name.substr(1))){
                                operand1 = globallatestValuesMap[(std::string)icmpInst->getOperand(0)->getNameOrAsOperand().substr(1)];
                                flag1=2;
                            }
                            else if(std::any_of(operand1Name.begin(), operand1Name.end(), ::isalpha) && globallatestValuesMap.count(operand1Name.substr(1))){
                                operand1 = globallatestValuesMap[(std::string)icmpInst->getOperand(0)->getNameOrAsOperand()];
                            }
                            else {
                                operand1 = (std::string)icmpInst->getOperand(0)->getNameOrAsOperand();
                            }

                            // OPERAND 2 CALCULATION
                            if (operand2Name.find('%')!=std::string::npos && latestValuesMap.count(operand2Name.substr(1))) {
                                operand2 = latestValuesMap[(std::string)icmpInst->getOperand(1)->getNameOrAsOperand().substr(1)];
                                flag2=1;
                            } 
                            else if(std::any_of(operand2Name.begin(), operand2Name.end(), ::isalpha) && latestValuesMap.count(operand2Name.substr(1))){
                                operand2 = latestValuesMap[(std::string)icmpInst->getOperand(1)->getNameOrAsOperand()];
                            }
                            else if(operand2Name.find('%')!=std::string::npos && globallatestValuesMap.count(operand2Name.substr(1))){
                                operand2 = globallatestValuesMap[(std::string)icmpInst->getOperand(1)->getNameOrAsOperand().substr(1)];
                                flag2=2;
                            }
                            else if(std::any_of(operand2Name.begin(), operand2Name.end(), ::isalpha) && globallatestValuesMap.count(operand2Name.substr(1))){
                                operand2 = globallatestValuesMap[(std::string)icmpInst->getOperand(1)->getNameOrAsOperand()];
                            }
                            else {
                                operand2 = (std::string)icmpInst->getOperand(1)->getNameOrAsOperand();
                            }

                            if(flag1==1 || flag1 == 2)
                                variableMap[lineNum][operand1Name.substr(1)] = (operand1=="")?"BOTTOM":operand1;
                            if(flag2==1 || flag2 == 2)
                                variableMap[lineNum][operand2Name.substr(1)] = (operand2=="")?"BOTTOM":operand2;
                            
                            std::string lhs_var = icmpInst->getName().str();
                            //// outs () <<"lhs var inside icmp instruction : " << lhs_var <<"\n";
                            variableMap[lineNum][lhs_var] = "BOTTOM";
                            if(firstAccess.find(lhs_var)==firstAccess.end()){
                                firstAccess.insert(lhs_var);
                            }
                        }
                        // CALL INST
                        else if(auto *callInst = dyn_cast<CallInst>(inst)){
                            Function *calledFunction = callInst->getCalledFunction();
                            if (calledFunction) {
                                std:: string lhs_var;
                                std::string instructionString;
                                raw_string_ostream instructionStream(instructionString);
                                callInst->print(instructionStream);
                                instructionString = instructionStream.str();
                                // ////// outs () << "the instruction string : "<<instructionString <<"\n";
                                size_t equalPos = instructionString.find("=");
                                if (equalPos != std::string::npos) {
                                    lhs_var = instructionString.substr(0, equalPos);                            // HANDLE THIS CASE REMEMBER
                                    lhs_var.erase(std::remove_if(lhs_var.begin(), lhs_var.end(), ::isspace), lhs_var.end());
                                    lhs_var = lhs_var.substr(1);
                                    variableMap[lineNum][lhs_var]="BOTTOM";
                                    if(firstAccess.find(lhs_var)==firstAccess.end()){
                                        firstAccess.insert(lhs_var);
                                    }
                                }
                                StringRef functionName = calledFunction->getName();
                                ////// outs () <<"functionName : " << functionName <<"\n";
                                if (functionName.find("scanf")!=std::string::npos) {
                                    ////// outs () << "found scanf " <<"\n";
                                    // Handle scanf call
                                    for (unsigned i = 1; i < callInst->getNumOperands(); ++i) {
                                        Value *operand = callInst->getOperand(i);
                                        if (operand->hasName()) {
                                            ////// outs () << "operand name inside scanf : "<< operand->getName().str() <<"\n";
                                            if(operand->getName().str().find("scanf")==std::string::npos){
                                                variableMap[lineNum][operand->getName().str()] = "BOTTOM";
                                                latestValuesMap[operand->getName().str()]="BOTTOM";
                                                globallatestValuesMap[operand->getName().str()]="BOTTOM";
                                                if(firstAccess.find(operand->getName().str())==firstAccess.end()){
                                                    firstAccess.insert(operand->getName().str());
                                                }
                                            }
                                        }
                                    }
                                } 
                                
                                else{
                                    
                                    std::string instStr;
                                    raw_string_ostream instStream(instStr);
                                    callInst->print(instStream);
                                    instStream.flush();

                                    // Find the position of the '=' character
                                    size_t equalPos = instStr.find("=");
                                    if (equalPos != std::string::npos) {
                                        // Extract the variables passed as arguments to printf
                                        size_t start = equalPos + 1;
                                        size_t end;
                                        do {
                                            // Find the next variable starting with '%'
                                            start = instStr.find("%", start);
                                            if (start != std::string::npos) {
                                                // Find the end of the variable name (next ',' or ')')
                                                end = instStr.find_first_of(",)", start);
                                                if (end != std::string::npos) {
                                                    // Extract the variable name
                                                    std::string varName = instStr.substr(start, end - start);
                                                    // std::string variableValue = variableMap[lineNum][varName.substr(1)];
                                                    if (varName[0] == '%') {
                                                        if(latestValuesMap.count(varName.substr(1)))
                                                            variableMap[lineNum][varName.substr(1)]=latestValuesMap[varName.substr(1)];
                                                        else
                                                            variableMap[lineNum][varName.substr(1)]=(globallatestValuesMap.count(varName.substr(1)))?globallatestValuesMap[varName.substr(1)]:"BOTTOM";

                                                    }
                                                    // Move to the next character after ',' or ')'
                                                    start = end + 1;
                                                }
                                            }
                                        } while (start != std::string::npos);
                                    }
                                    // meaning calling void type function
                                    else{
                                        vector<string>actualParams;
                                        // actualParams.push_back(calledFunctionName);
                                        size_t pos = 0;
                                        // Calculating the actual parameters of each function call, yeah ik, some string matching, but APIs are not working/ finding correct ones are pain
                                        while((pos = instructionString.find("noundef", pos)) != std::string::npos){
                                            bool addplustoconst = false;
                                            // outs ()<<"pos = "<<pos<<"\n";
                                            pos += 7;
                                            string varName = "";
                                            while (pos < instructionString.size() && std::isspace(instructionString[pos])) {
                                                ++pos;
                                            }
                                            if(pos < instructionString.size() && instructionString[pos]=='%'){
                                                pos++;
                                                while(pos < instructionString.size() && (instructionString[pos]!=','  && instructionString[pos]!=')')){
                                                    varName += instructionString[pos];
                                                    pos++;
                                                }
                                            }
                                            else if(pos < instructionString.size()){
                                                addplustoconst = true;
                                                while(pos < instructionString.size() && (instructionString[pos]!=','  && instructionString[pos]!=')')){
                                                    varName += instructionString[pos];
                                                    pos++;
                                                }
                                            }
                                            if(varName != "" && addplustoconst)
                                                actualParams.push_back("+"+ varName);
                                            else if(varName!="")
                                                actualParams.push_back(varName);
                                        }

                                        int sz=actualParams.size();

                                        if(sz>0){
                                            vector<string>temp;
                                            // temp.push_back(actualParams[0]);
                                            for(int i=0;i<(sz);i++){
                                                temp.push_back(actualParams[i]);
                                            }
                                            actualParams.clear();
                                            actualParams=temp;
                                        }
                                        for(auto x : actualParams){
                                            // outs ()<<"printing inside actualParams intra : " << x<< ",";
                                            if(latestValuesMap.count(x))
                                                variableMap[lineNum][x]=latestValuesMap[x];
                                            else if(x.find("+")!=string::npos)
                                                variableMap[lineNum][x]=x.substr(1);
                                            else
                                                variableMap[lineNum][x]=(globallatestValuesMap.count(x))?globallatestValuesMap[x]:"BOTTOM";
                                        }
                                        // outs ()<<"\n";
                                    }
                                }
                            }
                        }

                    }
                    // copy the values from latestValuesMap to the BBMap for predecessor propagation, while copying if there is change, then change=true
                    if(basicBlockVariableMap[CurrBB].empty()){
                        basicBlockVariableMap[CurrBB]=latestValuesMap;
                        change = true;
                    }
                    else{

                        auto currBBMap = basicBlockVariableMap[CurrBB];
                        // auto &latestValues = latestValuesMap;

                        bool allEqual = true; // Flag to track if all values are equal

                        for (auto pair : currBBMap) {
                            std::string variableName = pair.first;
                            std::string currValue = pair.second;

                            // Check if the variable exists in the latestValuesMap and has the same value
                            if (latestValuesMap.count(variableName) == 0 || (latestValuesMap.count(variableName) && latestValuesMap[variableName] != currValue)) {
                                allEqual = false;
                                break;
                            }
                        }

                        // If all values are not equal, set change to true
                        if (!allEqual) {
                            change = true;
                        }
                        basicBlockVariableMap[CurrBB]=latestValuesMap;

                    }
                    // if(change){

                        for (BasicBlock *SuccBB : successors(CurrBB)) {
                            if (visited.find(SuccBB)==visited.end()) {
                                worklist.push(SuccBB);
                                // Visited[SuccBB] = true;
                                visited.insert(SuccBB);
                            }
                            // }
                        }
                    // }
                                
            }

            return variableMap;
        }

        // ==============================================================================================

        bool runOnModule(Module &M) override {
            // write your code here
            
            int lineNum = 0;
            for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
                Function &Func = *F;
                std::string FuncName = Func.getName().str();
                allFunctions.insert(FuncName);
                lineNum = 0;
                // string currentBlockName = "";
                for (inst_iterator I = inst_begin(Func), E = inst_end(Func); I != E; ++I, ++lineNum) {
                    Instruction &Inst = *I;
                    std::string instStr;
                    raw_string_ostream instStream(instStr);
                    Inst.print(instStream);
                    globalinstructionLineMap[instStream.str()] = std::make_pair(FuncName, lineNum);

                    // CALL INST
                    if (auto *callInst = dyn_cast<CallInst>(&Inst)){
                        Function *calledFunction = callInst->getCalledFunction();
                        string calledFunctionName = calledFunction->getName().str();
                        if(calledFunctionName.find("scanf")!=string::npos || calledFunctionName.find("printf")!=string::npos)
                            continue;
                        // // outs () << "function i am calling : " << calledFunctionName << "\n";
                        if(calledFunction){
                            callInst->print(instStream);
                            string instructionString = instStream.str();
                            size_t equalPos = instructionString.find("=");
                            // meaning x = foo(a) type of function call
                            // if(equalPos != string::npos){

                            // }
                            // // meaning foo(a) type of function call
                            // else{

                            // }
                            vector<string>actualParams;
                            actualParams.push_back(calledFunctionName);
                            size_t pos = 0;
                            // Calculating the actual parameters of each function call, yeah ik, some string matching, but APIs are not working/ finding correct ones are pain
                            while((pos = instructionString.find("noundef", pos)) != std::string::npos){
                                bool addplustoconstant = false;
                                // // outs ()<<"pos = "<<pos<<"\n";
                                pos += 7;
                                string varName = "";
                                while (pos < instructionString.size() && std::isspace(instructionString[pos])) {
                                    ++pos;
                                }
                                if(pos < instructionString.size() && instructionString[pos]=='%'){
                                    pos++;
                                    while(pos < instructionString.size() && (instructionString[pos]!=','  && instructionString[pos]!=')')){
                                        varName += instructionString[pos];
                                        pos++;
                                    }
                                }
                                else if(pos < instructionString.size()){
                                    addplustoconstant = true;
                                    while(pos < instructionString.size() && (instructionString[pos]!=','  && instructionString[pos]!=')')){
                                        varName += instructionString[pos];
                                        pos++;
                                    }
                                }
                                if(varName != "" && addplustoconstant)
                                    actualParams.push_back("+" + varName);
                                else if(varName != "")
                                    actualParams.push_back(varName);
                            }
                           
                            int sz=actualParams.size();

                            if(sz>0){
                                vector<string>temp;
                                temp.push_back(actualParams[0]);
                                for(int i=1;i<=(sz-1)/2;i++){
                                    temp.push_back(actualParams[i]);
                                }
                                actualParams.clear();
                                actualParams=temp;
                            }


                            jumpFunction[FuncName][lineNum]=actualParams;
                            if(actualParams.size()>0){
                                vector<string>fp(actualParams.size()-1);
                                for(int i=0;i<fp.size();i++){
                                    fp[i]="TOP";
                                }
                                formalParams[calledFunctionName]=fp;
                            }
                            else
                                formalParams[calledFunctionName]=vector<string>();

                        }
                    }

                }
            }




            // queue to process the individual functions starting from main func & then Eval
            queue<pair<string,vector<string>>>WL;
            vector<string>passedVec;
            if(allFunctions.count("main"))
                WL.push(make_pair("main",passedVec));
            else if(allFunctions.size()>0){
                WL.push(make_pair(*(allFunctions.begin()),passedVec));
            }

            set<string>functionsVisited;

            int hardstop = 50;
            
            while(!WL.empty() && (hardstop--)){
                pair<string,vector<string>> callerFunction = WL.front();
                WL.pop();
                functionsVisited.insert(callerFunction.first);
                Function *Func = nullptr;
                for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
                    // Function &Func = *F;
                    Func = &(*F);
                    std::string FuncName = Func->getName().str();
                    if(FuncName==callerFunction.first){
                        break;
                    }
                }
                // outs ()<<"current function in queue : " << callerFunction.first << "\n";
                // in the order of callsites, the functions need to be added to the WL, and meet has to be taken before adding after doing doing intra const propagation
                if(callerFunction.first=="main"){
                    globalVariableMap["main"]=Eval(*Func,formalParams["main"]);
                }
                else{
                    // Eval on basis of whatever is pused to queue.second and meet between its formalParams, don't eval if no change
                    bool change = false;
                    vector<string>temp(callerFunction.second.size());
                    // outs ()<< "size of callerFunction.second.size() = "<< callerFunction.second.size() <<"\n";
                    // outs () << "size of formalParams[callerFunction.first].size() = " << formalParams[callerFunction.first].size() <<"\n";
                    if(callerFunction.second.size()==formalParams[callerFunction.first].size()){
                        for(int i=0;i<callerFunction.second.size();i++){
                            if(formalParams[callerFunction.first][i]!=callerFunction.second[i] && formalParams[callerFunction.first][i]=="BOTTOM")
                                temp[i]="BOTTOM";
                            else if(formalParams[callerFunction.first][i]!=callerFunction.second[i] && formalParams[callerFunction.first][i]=="TOP")
                                temp[i]=callerFunction.second[i];
                            else if(formalParams[callerFunction.first][i]!=callerFunction.second[i])
                                temp[i]="BOTTOM";
                            else    
                                temp[i]=callerFunction.second[i];
                        }

                        for(int i=0;i<temp.size();i++){
                            if(temp[i]!=formalParams[callerFunction.first][i]){
                                change = true;
                                break;
                            }
                        }
                    }
                    else{
                        // outs ()<< "Some serious problem here" << "\n";
                    }
                    if(change){
                        formalParams[callerFunction.first].clear();
                        formalParams[callerFunction.first]=temp;
                        globalVariableMap[callerFunction.first]=Eval(*Func,formalParams[callerFunction.first]);
                    }
                    
                }
                // map<string,map<int,vector<string>>>jumpFunction;    // function name -> lineNumbers -> {calledFunctionName, actualParams[0], actualParams[1],...}
                vector<pair<string,vector<string>>>functionsToBePushed;
                for(auto x : jumpFunction[callerFunction.first]){
                    map<string,string>M = globalVariableMap[callerFunction.first][x.first];
                    // jumpFunction[callerFunction.first][x.first]=
                    string fname = x.second[0];
                    
                    vector<string>temp;
                    for(int i=1;i<x.second.size();i++){
                        if(M.count(x.second[i]))
                            temp.push_back(M[x.second[i]]);
                    }
                    if(!temp.empty()){

                        functionsToBePushed.push_back(make_pair(fname,temp));
                    }

                }
                for(auto it:functionsToBePushed)
                    WL.push(it);
            }

            for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
                Function &Func = *F;
                std::string FuncName = Func.getName().str();
                // outs () << "the function name  : " << FuncName << "\n";
                map<int, map<string, string>>M;
                if(globalVariableMap.find(FuncName)==globalVariableMap.end())
                    continue;
                outs() << "Function Name : " <<FuncName << " : " << "\n";
                M = globalVariableMap[FuncName];
                int lastLine = 0;
                lastLine = M.rbegin()->first;
                // outs ()<< "last line of function map : " << lastLine << "\n";
                map<int,int>MyDefUseChain;
                set<string>VarsReachable;
                while(lastLine){
                    if(!M[lastLine].empty()){
                        bool allvarsbottomOrTainted = true;
                        for(auto x : M[lastLine]){
                            if((x.second == "BOTTOM" || VarsReachable.count(x.first)) && x.first.find("call")==string::npos){
                                // MyDefUseChain[lastLine]=1;
                                VarsReachable.insert(x.first);
                            }
                            else
                                allvarsbottomOrTainted = false;
                        }
                        if(allvarsbottomOrTainted)
                            MyDefUseChain[lastLine] = 1;

                    }
                    lastLine--;
                }

                int lineNum = 0;

                // transformation part happening here 

                vector<Instruction*> allocaInstToDelete;
                vector<Instruction*> otherInstToDelete;

                string currentBlockName = "";

                for (inst_iterator I = inst_begin(Func), E = inst_end(Func); I != E; ++I, ++lineNum) {
                    Instruction &Inst = *I;
                    std::string instStr;
                    raw_string_ostream instStream(instStr);
                    Inst.print(instStream);

                    std::string blockName = Inst.getParent()->getName().str();
    
                    if (blockName != currentBlockName) {
                        outs() << blockName << " : " <<" \n";
                        currentBlockName = blockName;
                    }


                    if(auto *callInst = dyn_cast<CallInst>(&Inst)){
                        Function *calledFunction = callInst->getCalledFunction();
                        string calledFunctionName = calledFunction->getName().str();
                        if(calledFunctionName.find("scanf")!=string::npos){
                            // continue;
                            outs() << Inst << "\n";
                        }
                            
                        // else if print statement, depending on bottom , or constant, print and replace
                        else if(calledFunctionName.find("printf")!=string::npos){
                            if(MyDefUseChain[lineNum]==1){
                                outs() << Inst << "\n";
                                // continue;
                            }
                            // replace with constants
                            else{
                                // outs () << "entering here to replace printf: " << "\n";
                                if (M.find(lineNum) != M.end()) {

                                    for (auto &var : M[lineNum]) {
                                        // Get the variable name and value from the map
                                        std::string varName = "%" + var.first;
                                        std::string varValue = var.second;
                                        if (var.first.find("call")!=string::npos || varValue == "BOTTOM")
                                            continue;
                                        // Replace all occurrences of varName in the instruction
                                        size_t pos = instStr.find(varName);
                                        while (pos != std::string::npos) {
                                            // Check if varName is a separate word in the instruction
                                            if ((pos == 0 || !isalnum(instStr[pos - 1])) &&
                                                (pos + varName.length() == instStr.length() || !isalnum(instStr[pos + varName.length()]))) {
                                                // Replace varName with varValue
                                                instStr.replace(pos, varName.length(), varValue);
                                            }
                                            // Find the next occurrence of varName
                                            pos = instStr.find(varName, pos + varValue.length());
                                        }
                                    }
                                }

                               
                                outs() << instStr << "\n";
                            }
                        }
                        // else pure diff function call, again depending on bottom or not, replace
                        else{
                            // outs () << "entering here to replace other function calls as per my use def chain " << "\n";
                            if(MyDefUseChain[lineNum]==1){
                                outs() << Inst << "\n";
                                // continue;
                            }
                            else{
                                if (M.find(lineNum) != M.end()) {

                                    for (auto &var : M[lineNum]) {
                                        // Get the variable name and value from the map
                                        std::string varName = "%" + var.first;
                                        std::string varValue = var.second;
                                        if (var.first.find("call")!=string::npos || varValue == "BOTTOM")
                                            continue;
                                        // Replace all occurrences of varName in the instruction
                                        size_t pos = instStr.find(varName);
                                        while (pos != std::string::npos) {
                                            // Check if varName is a separate word in the instruction
                                            if ((pos == 0 || !isalnum(instStr[pos - 1])) &&
                                                (pos + varName.length() == instStr.length() || !isalnum(instStr[pos + varName.length()]))) {
                                                // Replace varName with varValue
                                                instStr.replace(pos, varName.length(), varValue);
                                            }
                                            // Find the next occurrence of varName
                                            pos = instStr.find(varName, pos + varValue.length());
                                        }
                                    }

                                }

                                
                                outs() << instStr << "\n";
                            }
                        }
                    }
                    else{
                        if(MyDefUseChain[lineNum]==1){
                            outs() << Inst <<"\n";
                            // continue;
                        }
                        else
                            otherInstToDelete.push_back(&Inst);
                    }
                }   // end of function iterator, iterating across all instructions

               
            }         // end of module iterator, iterating accross all functions

            return false;
        }

        // ========================================================================================


  }; // end of struct cons_eval
}  // end of anonymous namespace

char cons_eval::ID = 0;
static RegisterPass<cons_eval> X("cons_eval_given", "Constant Propagation Pass for Assignment");