/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A5Header.h"
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

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    WorkList<unsigned> workList;

    // === Address rule 初始化 ===
    for (auto it = consg->begin(); it != consg->end(); ++it)
    {
        ConstraintNode *node = it->second;
        unsigned p = node->getId();

        for (auto edge : node->getAddrOutEdges())
        {
            auto addrEdge = SVFUtil::dyn_cast<AddrCGEdge>(edge);
            if (!addrEdge) continue;

            NodeID o = addrEdge->getDstID();
            pts[p].insert(o);
            workList.push(p);
        }
    }

    // === 主循环 ===
    while (!workList.empty())
    {
        NodeID p = workList.pop();
        ConstraintNode *nodeP = consg->getGNode(p);
        if (!nodeP) continue;

        // --- Store rule ---
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

        // --- Load rule ---
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

        // --- Copy rule ---
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

        // --- Gep rule ---
        for (auto edge : nodeP->getGepOutEdges())
        {
            auto gepEdge = SVFUtil::dyn_cast<GepCGEdge>(edge);
            if (!gepEdge) continue;

            NodeID x = gepEdge->getDstID();
            size_t oldSize = pts[x].size();
            for (auto o : pts[p])
            {
                // 直接把 gepEdge 指针传给 getGepObjVar
                NodeID fld = consg->getGepObjVar(o, gepEdge->getDstID()); // 版本：getGepObjVar(id, GepCGEdge*)
                pts[x].insert(fld);
            }
            if (pts[x].size() != oldSize) workList.push(x);
        }
    }
}