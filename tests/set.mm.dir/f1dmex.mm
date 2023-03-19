include "wf1.mm"
include "wcel.mm"
include "cvv.mm"
include "crn.mm"
include "ccnv.mm"
include "wfo.mm"
include "wss.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "ssexg.mm"
include "sylan.mm"
include "ex.mm"
include "wf1o.mm"
include "f1cnv.mm"
include "f1ofo.mm"
include "fornex.mm"
include "syl6ci.mm"
include "imp.mm"

theorem f1dmex
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ B e. C ) -> A e. _V )

  proof
    cA
    cB
    cF
    wf1
    #
    cB
    cC
    wcel
    #
    cA
    cvv
    wcel
    #
    @0
    @1
    cF
    crn
    #
    cvv
    wcel
    #
    @3
    cA
    cF
    ccnv
    #
    wfo
    #
    @2
    @0
    @1
    @4
    @0
    @3
    cB
    wss
    #
    @1
    @4
    @0
    cA
    cB
    cF
    wf
    @7
    cA
    cB
    cF
    f1f
    cA
    cB
    cF
    frn
    syl
    @3
    cB
    cC
    ssexg
    sylan
    ex
    @0
    @3
    cA
    @5
    wf1o
    @6
    cA
    cB
    cF
    f1cnv
    @3
    cA
    @5
    f1ofo
    syl
    @3
    cA
    cvv
    @5
    fornex
    syl6ci
    imp
end
