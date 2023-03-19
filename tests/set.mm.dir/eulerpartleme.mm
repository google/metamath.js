include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "wf.mm"
include "w3a.mm"
include "nn0ex.mm"
include "nnex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem eulerpartleme
  let cA: class A
  let cP: class P
  let vf: setvar f
  let vk: setvar k
  let cN: class N
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint N f
  assert |- ( A e. P <-> ( A : NN --> NN0 /\ ( `' A " NN ) e. Fin /\ sum_ k e. NN ( ( A ` k ) x. k ) = N ) )

  proof
    cA
    cn0
    cn
    cmap
    co
    #
    wcel
    #
    cA
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    cn
    vk
    cv
    #
    cA
    cfv
    #
    @5
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    wa
    #
    wa
    cn
    cn0
    cA
    wf
    #
    @10
    wa
    cA
    cP
    wcel
    @11
    @4
    @9
    w3a
    @1
    @11
    @10
    cn0
    cn
    cA
    nn0ex
    nnex
    elmap
    anbi1i
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    #
    cn
    @5
    @12
    cfv
    #
    @5
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    wa
    @10
    vf
    cA
    @0
    cP
    @12
    cA
    wceq
    #
    @15
    @4
    @19
    @9
    @20
    @14
    @3
    cfn
    @20
    @13
    @2
    cn
    @12
    cA
    cnveq
    imaeq1d
    eleq1d
    @20
    @18
    @8
    cN
    @20
    cn
    @17
    @7
    vk
    @20
    @16
    @6
    @5
    cmul
    @5
    @12
    cA
    fveq1
    oveq1d
    sumeq2sdv
    eqeq1d
    anbi12d
    eulerpart.p
    elrab2
    @11
    @4
    @9
    3anass
    3bitr4i
end
