include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cvv.mm"
include "cpw.mm"
include "xpexg.mm"
include "pwexg.mm"
include "wss.mm"
include "cv.mm"
include "cab.mm"
include "wf.mm"
include "fssxp.mm"
include "selpw.mm"
include "sylibr.mm"
include "anim1i.mm"
include "ss2abi.mm"
include "eqsstri.mm"
include "ssab2.mm"
include "sstri.mm"
include "ssexg.mm"
include "mpan.mm"
include "3syl.mm"

theorem fabexg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume fabexg.1: |- F = { x | ( x : A --> B /\ ph ) }

  disjoint A x
  disjoint B x
  assert |- ( ( A e. C /\ B e. D ) -> F e. _V )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    cA
    cB
    cxp
    #
    cvv
    wcel
    @0
    cpw
    #
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    cA
    cB
    cC
    cD
    xpexg
    @0
    cvv
    pwexg
    cF
    @1
    wss
    @2
    @3
    cF
    vx
    cv
    #
    @1
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @1
    cF
    cA
    cB
    @4
    wf
    #
    wph
    wa
    #
    vx
    cab
    @7
    fabexg.1
    @9
    @6
    vx
    @8
    @5
    wph
    @8
    @4
    @0
    wss
    @5
    cA
    cB
    @4
    fssxp
    vx
    @0
    selpw
    sylibr
    anim1i
    ss2abi
    eqsstri
    wph
    vx
    @1
    ssab2
    sstri
    cF
    @1
    cvv
    ssexg
    mpan
    3syl
end
