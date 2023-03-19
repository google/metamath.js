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
include "dmmpt2ssx.mm"
include "snex.mm"
include "xpexg.mm"
include "mpan.mm"
include "ralimi.mm"
include "iunexg.mm"
include "sylan2.mm"
include "ssexg.mm"
include "sylancr.mm"
include "funex.mm"

theorem mpt2exxg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume mpt2exg.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( ( A e. R /\ A. x e. A B e. S ) -> F e. _V )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    vx
    cA
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
    mpt2exg.1
    mpt2fun
    @3
    @4
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
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
    mpt2exg.1
    dmmpt2ssx
    @2
    @0
    @8
    cvv
    wcel
    #
    vx
    cA
    wral
    @10
    @1
    @11
    vx
    cA
    @7
    cvv
    wcel
    @1
    @11
    @6
    snex
    @7
    cB
    cvv
    cS
    xpexg
    mpan
    ralimi
    vx
    cA
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
