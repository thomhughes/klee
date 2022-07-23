//===-- ExecutorUtil.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Context.h"
#include "Executor.h"

#include "klee/Config/Version.h"
#include "klee/Core/Interpreter.h"
#include "klee/Expr/Expr.h"
#include "klee/Module/KModule.h"
#include "klee/Solver/Solver.h"
#include "klee/Support/ErrorHandling.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>

using namespace llvm;

namespace klee {

  ref<klee::Expr> Executor::evalConstant(const Constant *c,
                                                 const KInstruction *ki) {
    if (!ki) {
      KConstant* kc = kmodule->getKConstant(c);
      if (kc)
        ki = kc->ki;
    }

    if (const llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      return evalConstantExpr(ce, ki);
    } else {
      if (const ConstantInt *ci = dyn_cast<ConstantInt>(c)) {
        return ConstantExpr::alloc(ci->getValue());
      } else if (const ConstantFP *cf = dyn_cast<ConstantFP>(c)) {
        return FConstantExpr::alloc(cf->getValue());
      } else if (const GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
        auto it = globalAddresses.find(gv);
        assert(it != globalAddresses.end());
        return it->second;
      } else if (isa<ConstantPointerNull>(c)) {
        return Expr::createPointer(0);
      } else if (isa<UndefValue>(c) || isa<ConstantAggregateZero>(c)) {
        if (getWidthForLLVMType(c->getType()) == 0) {
          if (isa<llvm::LandingPadInst>(ki->inst)) {
            klee_warning_once(0, "Using zero size array fix for landingpad instruction filter");
            return ConstantExpr::create(0, 1);
          }
        }
        return ConstantExpr::create(0, getWidthForLLVMType(c->getType()));
      } else if (const ConstantDataSequential *cds =
                 dyn_cast<ConstantDataSequential>(c)) {
        // Handle a vector or array: first element has the smallest address,
        // the last element the highest
        std::vector<ref<Expr> > kids;
        for (unsigned i = cds->getNumElements(); i != 0; --i) {
          ref<Expr> kid = evalConstant(cds->getElementAsConstant(i - 1), ki);
          kids.push_back(kid);
        }
        assert(Context::get().isLittleEndian() &&
               "FIXME:Broken for big endian");
        ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
        return cast<ConstantExpr>(res);
      } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
        const StructLayout *sl = kmodule->targetData->getStructLayout(cs->getType());
        llvm::SmallVector<ref<Expr>, 4> kids;
        for (unsigned i = cs->getNumOperands(); i != 0; --i) {
          unsigned op = i-1;
          ref<Expr> kid = evalConstant(cs->getOperand(op), ki);

          uint64_t thisOffset = sl->getElementOffsetInBits(op),
            nextOffset = (op == cs->getNumOperands() - 1)
            ? sl->getSizeInBits()
            : sl->getElementOffsetInBits(op+1);
          if (nextOffset-thisOffset > kid->getWidth()) {
            uint64_t paddingWidth = nextOffset-thisOffset-kid->getWidth();
            kids.push_back(ConstantExpr::create(0, paddingWidth));
          }

          kids.push_back(kid);
        }
        assert(Context::get().isLittleEndian() &&
               "FIXME:Broken for big endian");
        ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
        return cast<ConstantExpr>(res);
      } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)){
        llvm::SmallVector<ref<Expr>, 4> kids;
        for (unsigned i = ca->getNumOperands(); i != 0; --i) {
          unsigned op = i-1;
          ref<Expr> kid = evalConstant(ca->getOperand(op), ki);
          kids.push_back(kid);
        }
        assert(Context::get().isLittleEndian() &&
               "FIXME:Broken for big endian");
        ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
        return cast<ConstantExpr>(res);
      } else if (const ConstantVector *cv = dyn_cast<ConstantVector>(c)) {
        llvm::SmallVector<ref<Expr>, 8> kids;
        const size_t numOperands = cv->getNumOperands();
        kids.reserve(numOperands);
        for (unsigned i = numOperands; i != 0; --i) {
          kids.push_back(evalConstant(cv->getOperand(i - 1), ki));
        }
        assert(Context::get().isLittleEndian() &&
               "FIXME:Broken for big endian");
        ref<Expr> res = ConcatExpr::createN(numOperands, kids.data());
        assert(isa<ConstantExpr>(res) &&
               "result of constant vector built is not a constant");
        return cast<ConstantExpr>(res);
      } else if (const BlockAddress * ba = dyn_cast<BlockAddress>(c)) {
        // return the address of the specified basic block in the specified function
        const auto arg_bb = (BasicBlock *) ba->getOperand(1);
        const auto res = Expr::createPointer(reinterpret_cast<std::uint64_t>(arg_bb));
        return cast<ConstantExpr>(res);
      } else {
        std::string msg("Cannot handle constant ");
        llvm::raw_string_ostream os(msg);
        os << "'" << *c << "' at location "
           << (ki ? ki->getSourceLocation() : "[unknown]");
        klee_error("%s", os.str().c_str());
      }
    }
  }

  ref<Expr> Executor::evalConstantExpr(const llvm::ConstantExpr *ce,
                                               const KInstruction *ki) {
    llvm::Type *type = ce->getType();

    ref<Expr> op1(0), op2(0), op3(0);
    int numOperands = ce->getNumOperands();

    if (numOperands > 0) op1 = evalConstant(ce->getOperand(0), ki);
    if (numOperands > 1) op2 = evalConstant(ce->getOperand(1), ki);
    if (numOperands > 2) op3 = evalConstant(ce->getOperand(2), ki);

    /* Checking for possible errors during constant folding */
    switch (ce->getOpcode()) {
    case Instruction::SDiv:
    case Instruction::UDiv:
    case Instruction::SRem:
    case Instruction::URem:
      if (cast<ConstantExpr>(op2)->getLimitedValue() == 0) {
        std::string msg("Division/modulo by zero during constant folding at location ");
        llvm::raw_string_ostream os(msg);
        os << (ki ? ki->getSourceLocation() : "[unknown]");
        klee_error("%s", os.str().c_str());
      }
      break;
    case Instruction::FDiv:
    case Instruction::FRem:
        if (cast<FConstantExpr>(op2)->getLimitedValue() == 0) {
            std::string msg("Division/modulo by zero during constant folding at location ");
            llvm::raw_string_ostream os(msg);
            os << (ki ? ki->getSourceLocation() : "[unknown]");
            klee_error("%s", os.str().c_str());
        }
        break;
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
      if (cast<ConstantExpr>(op2)->getLimitedValue() >= cast<ConstantExpr>(op1)->getWidth()) {
        std::string msg("Overshift during constant folding at location ");
        llvm::raw_string_ostream os(msg);
        os << (ki ? ki->getSourceLocation() : "[unknown]");
        klee_error("%s", os.str().c_str());
      }
    }

    std::string msg("Unknown ConstantExpr type");
    llvm::raw_string_ostream os(msg);

    switch (ce->getOpcode()) {
    default :
      os << "'" << *ce << "' at location "
         << (ki ? ki->getSourceLocation() : "[unknown]");
      klee_error("%s", os.str().c_str());

    case Instruction::Trunc:
      return cast<ConstantExpr>(op1)->Extract(0, getWidthForLLVMType(type));
    case Instruction::ZExt:  return cast<ConstantExpr>(op1)->ZExt(getWidthForLLVMType(type));
    case Instruction::SExt:  return cast<ConstantExpr>(op1)->SExt(getWidthForLLVMType(type));
    case Instruction::Add:   return cast<ConstantExpr>(op1)->Add(cast<ConstantExpr>(op2));
    case Instruction::Sub:   return cast<ConstantExpr>(op1)->Sub(cast<ConstantExpr>(op2));
    case Instruction::Mul:   return cast<ConstantExpr>(op1)->Mul(cast<ConstantExpr>(op2));
    case Instruction::SDiv:  return cast<ConstantExpr>(op1)->SDiv(cast<ConstantExpr>(op2));
    case Instruction::UDiv:  return cast<ConstantExpr>(op1)->UDiv(cast<ConstantExpr>(op2));
    case Instruction::SRem:  return cast<ConstantExpr>(op1)->SRem(cast<ConstantExpr>(op2));
    case Instruction::URem:  return cast<ConstantExpr>(op1)->URem(cast<ConstantExpr>(op2));
    case Instruction::And:   return cast<ConstantExpr>(op1)->And(cast<ConstantExpr>(op2));
    case Instruction::Or:    return cast<ConstantExpr>(op1)->Or(cast<ConstantExpr>(op2));
    case Instruction::Xor:   return cast<ConstantExpr>(op1)->Xor(cast<ConstantExpr>(op2));
    case Instruction::Shl:   return cast<ConstantExpr>(op1)->Shl(cast<ConstantExpr>(op2));
    case Instruction::LShr:  return cast<ConstantExpr>(op1)->LShr(cast<ConstantExpr>(op2));
    case Instruction::AShr:  return cast<ConstantExpr>(op1)->AShr(cast<ConstantExpr>(op2));
    case Instruction::BitCast:  return op1;

    case Instruction::IntToPtr:
      return cast<ConstantExpr>(op1)->ZExt(getWidthForLLVMType(type));

    case Instruction::PtrToInt:
      return cast<ConstantExpr>(op1)->ZExt(getWidthForLLVMType(type));

    case Instruction::GetElementPtr: {
      ref<ConstantExpr> base = cast<ConstantExpr>(op1)->ZExt(Context::get().getPointerWidth());
      for (gep_type_iterator ii = gep_type_begin(ce), ie = gep_type_end(ce);
           ii != ie; ++ii) {
        ref<ConstantExpr> indexOp =
            evalConstant(cast<Constant>(ii.getOperand()), ki);
        if (indexOp->isZero())
          continue;

        // Handle a struct index, which adds its field offset to the pointer.
        if (auto STy = ii.getStructTypeOrNull()) {
          unsigned ElementIdx = indexOp->getZExtValue();
          const StructLayout *SL = kmodule->targetData->getStructLayout(STy);
          base = base->Add(
              ConstantExpr::alloc(APInt(Context::get().getPointerWidth(),
                                        SL->getElementOffset(ElementIdx))));
          continue;
        }

        // For array or vector indices, scale the index by the size of the type.
        // Indices can be negative
        base = base->Add(indexOp->SExt(Context::get().getPointerWidth())
                             ->Mul(ConstantExpr::alloc(
                                 APInt(Context::get().getPointerWidth(),
                                       kmodule->targetData->getTypeAllocSize(
                                           ii.getIndexedType())))));
      }
      return base;
    }

    case Instruction::ICmp: {
      switch(ce->getPredicate()) {
      default: assert(0 && "unhandled ICmp predicate");
      case ICmpInst::ICMP_EQ:  return cast<ConstantExpr>(op1)->Eq(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_NE:  return cast<ConstantExpr>(op1)->Ne(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_UGT: return cast<ConstantExpr>(op1)->Ugt(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_UGE: return cast<ConstantExpr>(op1)->Uge(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_ULT: return cast<ConstantExpr>(op1)->Ult(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_ULE: return cast<ConstantExpr>(op1)->Ule(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_SGT: return cast<ConstantExpr>(op1)->Sgt(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_SGE: return cast<ConstantExpr>(op1)->Sge(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_SLT: return cast<ConstantExpr>(op1)->Slt(cast<ConstantExpr>(op2));
      case ICmpInst::ICMP_SLE: return cast<ConstantExpr>(op1)->Sle(cast<ConstantExpr>(op2));
      }
    }

    case Instruction::Select:
      return op1->isTrue() ? op2 : op3;

    case Instruction::FAdd: return cast<FConstantExpr>(op1)->FAdd(cast<FConstantExpr>(op2));
    case Instruction::FSub: return cast<FConstantExpr>(op1)->FSub(cast<FConstantExpr>(op2));
    case Instruction::FMul: return cast<FConstantExpr>(op1)->FMul(cast<FConstantExpr>(op2));
    case Instruction::FDiv: return cast<FConstantExpr>(op1)->FDiv(cast<FConstantExpr>(op2));
    case Instruction::FRem: return cast<FConstantExpr>(op1)->FRem(cast<FConstantExpr>(op2));
    case Instruction::FPTrunc: // TODO: Check if this works?
    case Instruction::FPExt: return cast<FConstantExpr>(op1)->FExt(getWidthForLLVMType(type));
    case Instruction::UIToFP: return cast<ConstantExpr>(op1)->UToF(getWidthForLLVMType(type));
    case Instruction::SIToFP: return cast<ConstantExpr>(op1)->SToF(getWidthForLLVMType(type));
    case Instruction::FPToUI: return cast<FConstantExpr>(op1)->FToU(getWidthForLLVMType(type));
    case Instruction::FPToSI: return cast<FConstantExpr>(op1)->FToS(getWidthForLLVMType(type));
    case Instruction::FCmp: {
        switch(ce->getPredicate()) {
            default: assert(0 && "unhandled FCmp predicate");
            case FCmpInst::FCMP_FALSE: return FConstantExpr::create(false, getWidthForLLVMType(type));
	        case FCmpInst::FCMP_OEQ: return cast<FConstantExpr>(op1)->FOeq(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_OGT: return cast<FConstantExpr>(op1)->FOgt(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_OGE: return cast<FConstantExpr>(op1)->FOge(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_OLT: return cast<FConstantExpr>(op1)->FOlt(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_OLE: return cast<FConstantExpr>(op1)->FOle(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_ONE: return cast<FConstantExpr>(op1)->FOne(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_ORD: return cast<FConstantExpr>(op1)->FOrd(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_UNO: return cast<FConstantExpr>(op1)->FUno(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_UEQ: return cast<FConstantExpr>(op1)->FUeq(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_UGT: return cast<FConstantExpr>(op1)->FUgt(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_UGE: return cast<FConstantExpr>(op1)->FUge(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_ULT: return cast<FConstantExpr>(op1)->FUlt(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_ULE: return cast<FConstantExpr>(op1)->FUle(cast<FConstantExpr>(op2));
            case FCmpInst::FCMP_UNE: return cast<FConstantExpr>(op1)->FUne(cast<FConstantExpr>(op2));
	        case FCmpInst::FCMP_TRUE: return FConstantExpr::create(true, getWidthForLLVMType(type));
        }
    }
    }
  }
}
