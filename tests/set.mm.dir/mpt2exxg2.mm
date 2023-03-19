include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wfun.mm"
include "cdm.mm"
include "cvv.mm"
include "mpt2fun.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wss.mm"
include "dmmpt2ssx2.mm"
include "snex.mm"
include "xpexg.mm"
include "mpan2.mm"
include "ralimi.mm"
include "iunexg.mm"
include "sylan2.mm"
include "ssexg.mm"
include "sylancr.mm"
include "funex.mm"

theorem mpt2exxg2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vk: setvar k
  assume mpt2exxg2.1: |- F = ( x e. A , y e. B |-> C )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint A x
  disjoint k x
  assert |- ( ( B e. R /\ A. y e. B A e. S ) -> F e. _V )

  proof
    cB
    cR
    wcel
    #
    cA
    cS
    wcel
    #
    vy
    cB
    wral
    #
    wa
    #
    cF
    wfun
    cF
    cdm
    #
    cvv
    wcel
    #
    cF
    cvv
    wcel
    vx
    vy
    cA
    cB
    cC
    cF
    mpt2exxg2.1
    mpt2fun
    @3
    @4
    vy
    cB
    cA
    vy
    cv
    #
    csn
    #
    cxp
    #
    ciun
    #
    wss
    @9
    cvv
    wcel
    #
    @5
    vx
    vy
    cA
    cB
    cC
    cF
    mpt2exxg2.1
    dmmpt2ssx2
    @2
    @0
    @8
    cvv
    wcel
    #
    vy
    cB
    wral
    @10
    @1
    @11
    vy
    cB
    @1
    @7
    cvv
    wcel
    @11
    @6
    snex
    cA
    @7
    cS
    cvv
    xpexg
    mpan2
    ralimi
    vy
    cB
    @8
    cR
    cvv
    iunexg
    sylan2
    @4
    @9
    cvv
    ssexg
    sylancr
    cvv
    cF
    funex
    sylancr
end
