include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "cvv.mm"
include "fssxp.mm"
include "ss2abi.mm"
include "df-pw.mm"
include "sseqtr4i.mm"
include "xpexg.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem mapex
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f

  disjoint A f
  disjoint B f
  assert |- ( ( A e. C /\ B e. D ) -> { f | f : A --> B } e. _V )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    vf
    cab
    #
    cA
    cB
    cxp
    #
    cpw
    #
    wss
    @5
    cvv
    wcel
    #
    @3
    cvv
    wcel
    @3
    @1
    @4
    wss
    #
    vf
    cab
    @5
    @2
    @7
    vf
    cA
    cB
    @1
    fssxp
    ss2abi
    vf
    @4
    df-pw
    sseqtr4i
    @0
    @4
    cvv
    wcel
    @6
    cA
    cB
    cC
    cD
    xpexg
    @4
    cvv
    pwexg
    syl
    @3
    @5
    cvv
    ssexg
    sylancr
end
