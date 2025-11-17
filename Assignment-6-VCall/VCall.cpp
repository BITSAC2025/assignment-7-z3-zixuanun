/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A6Header.h"
#include "Graphs/ConsG.h"
#include "Graphs/ConsGNode.h"
#include "Graphs/ConsGEdge.h"
#include "Util/SVFUtil.h"
#include "Util/WorkList.h"
using namespace llvm;
using namespace std;
using namespace SVF;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump("consg");

    Andersen andersen(consg);
    const SVF::CallGraph *pcg = pag->getCallGraph();
    SVF::CallGraph *cg = const_cast<SVF::CallGraph*>(pcg);
    // auto cg = pag->getCallGraph();

    // TODO: complete the following two methods
    andersen.runPointerAnalysis();
    andersen.updateCallGraph(cg);

    cg->dump("callgraph");
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    WorkList<NodeID> workList;

    // Address rule
    for (auto it = consg->begin(); it != consg->end(); ++it)
    {
        ConstraintNode *node = it->second;
        if (!node) continue;
        NodeID p = node->getId();

        for (auto edge : node->getAddrOutEdges())
        {
            auto addrEdge = SVFUtil::dyn_cast<AddrCGEdge>(edge);
            if (!addrEdge) continue;

            NodeID o = addrEdge->getDstID();
            pts[p].insert(o);
            workList.push(p);
        }
    }

    // Propagation
    while (!workList.empty())
    {
        NodeID p = workList.pop();
        ConstraintNode *nodeP = consg->getGNode(p);
        if (!nodeP) continue;

        // Store rule
        for (auto edge : nodeP->getStoreOutEdges())
        {
            auto storeEdge = SVFUtil::dyn_cast<StoreCGEdge>(edge);
            if (!storeEdge) continue;

            NodeID q = storeEdge->getDstID();
            for (auto o : pts[p])
            {
                ConstraintNode *srcNode = consg->getGNode(q);
                ConstraintNode *dstNode = consg->getGNode(o);
                if (!consg->hasEdge(srcNode, dstNode, ConstraintEdge::Copy))
                {
                    consg->addCopyCGEdge(srcNode->getId(), dstNode->getId());
                    workList.push(q);
                }
            }
        }

        // Load rule
        for (auto edge : nodeP->getLoadOutEdges())
        {
            auto loadEdge = SVFUtil::dyn_cast<LoadCGEdge>(edge);
            if (!loadEdge) continue;

            NodeID r = loadEdge->getDstID();
            for (auto o : pts[p])
            {
                ConstraintNode *srcNode = consg->getGNode(o);
                ConstraintNode *dstNode = consg->getGNode(r);
                if (!consg->hasEdge(srcNode, dstNode, ConstraintEdge::Copy))
                {
                    consg->addCopyCGEdge(srcNode->getId(), dstNode->getId());
                    workList.push(r);
                }
            }
        }

        // Copy rule
        for (auto edge : nodeP->getCopyOutEdges())
        {
            auto copyEdge = SVFUtil::dyn_cast<CopyCGEdge>(edge);
            if (!copyEdge) continue;

            NodeID x = copyEdge->getDstID();
            size_t oldSize = pts[x].size();
            pts[x].insert(pts[p].begin(), pts[p].end());
            if (pts[x].size() != oldSize)
                workList.push(x);
        }

        // Gep rule
        for (auto edge : nodeP->getGepOutEdges())
        {
            auto gepEdge = SVFUtil::dyn_cast<GepCGEdge>(edge);
            if (!gepEdge) continue;

            NodeID x = gepEdge->getDstID();
            size_t oldSize = pts[x].size();
            for (auto o : pts[p])
            {
                NodeID fld = consg->getGepObjVar(o, gepEdge->getDstID());
                pts[x].insert(fld);
            }
            if (pts[x].size() != oldSize) workList.push(x);
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    if (!consg || !cg) return;
    // TODO: complete this method.
    //  The implementation of call graph is provided in the SVF library
    // 获取所有间接调用点
    const auto &indirectCalls = consg->getIndirectCallsites();

    // 遍历每个调用点
    for (auto &csPair : indirectCalls)
    {
        const CallICFGNode *cs = csPair.first;   // 调用点节点
        NodeID funPtrId = csPair.second;         // 函数指针变量ID

        // 获取指针指向的函数集合
        auto it = pts.find(funPtrId);
        if (it == pts.end()) continue;

        const FunObjVar *callerFun = cs->getCaller();

        // 遍历函数指针的目标集合
        for (auto target : it->second)
        {
            ConstraintNode *tNode = consg->getGNode(target);
            if (!tNode) continue;
            const FunObjVar *calleeFun = SVFUtil::dyn_cast<FunObjVar>(tNode);
            if (calleeFun)
            {
                // addIndirectCallGraphEdge(const CallICFGNode* cs,
                //                          const FunObjVar* callerFun,
                //                          const FunObjVar* calleeFun)
                cg->addIndirectCallGraphEdge(cs, callerFun, calleeFun);
            }
        }
    }
}