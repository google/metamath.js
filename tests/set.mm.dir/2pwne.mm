include "wcel.mm"
include "cpw.mm"
include "wceq.mm"
include "csdm.mm"
include "wbr.mm"
include "sdomirr.mm"
include "canth2g.mm"
include "cvv.mm"
include "pwexg.mm"
include "syl.mm"
include "sdomtr.mm"
include "syl2anc.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "mtoi.mm"
include "neqned.mm"

theorem 2pwne
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ~P ~P A =/= A )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    cpw
    #
    cA
    @0
    @2
    cA
    wceq
    #
    @2
    @2
    csdm
    wbr
    #
    @2
    sdomirr
    @0
    @4
    @3
    cA
    @2
    csdm
    wbr
    #
    @0
    cA
    @1
    csdm
    wbr
    @1
    @2
    csdm
    wbr
    #
    @5
    cA
    cV
    canth2g
    @0
    @1
    cvv
    wcel
    @6
    cA
    cV
    pwexg
    @1
    cvv
    canth2g
    syl
    cA
    @1
    @2
    sdomtr
    syl2anc
    @2
    cA
    @2
    csdm
    breq1
    syl5ibrcom
    mtoi
    neqned
end
