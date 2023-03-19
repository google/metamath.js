include "wcel.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "ciun.mm"
include "cqs.mm"
include "cima.mm"
include "cvv.mm"
include "wral.mm"
include "ecexg.mm"
include "ralrimivw.mm"
include "dfiun2g.mm"
include "syl.mm"
include "eqcomd.mm"
include "df-qs.mm"
include "unieqi.mm"
include "csn.mm"
include "df-ec.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "imaiun.mm"
include "iunid.mm"
include "imaeq2i.mm"
include "3eqtr2ri.mm"
include "3eqtr4g.mm"

theorem uniqs
  let cA: class A
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. V -> U. ( A /. R ) = ( R " A ) )

  proof
    cR
    cV
    wcel
    #
    vy
    cv
    vx
    cv
    #
    cR
    cec
    #
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cuni
    #
    vx
    cA
    @2
    ciun
    #
    cA
    cR
    cqs
    #
    cuni
    cR
    cA
    cima
    #
    @0
    @5
    @4
    @0
    @2
    cvv
    wcel
    #
    vx
    cA
    wral
    @5
    @4
    wceq
    @0
    @8
    vx
    cA
    @1
    cV
    cR
    ecexg
    ralrimivw
    vx
    vy
    cA
    @2
    cvv
    dfiun2g
    syl
    eqcomd
    @6
    @3
    vx
    vy
    cA
    cR
    df-qs
    unieqi
    @5
    vx
    cA
    cR
    @1
    csn
    #
    cima
    #
    ciun
    cR
    vx
    cA
    @9
    ciun
    #
    cima
    @7
    vx
    cA
    @2
    @10
    @2
    @10
    wceq
    @1
    cA
    wcel
    @1
    cR
    df-ec
    a1i
    iuneq2i
    vx
    cR
    cA
    @9
    imaiun
    @11
    cA
    cR
    vx
    cA
    iunid
    imaeq2i
    3eqtr2ri
    3eqtr4g
end
