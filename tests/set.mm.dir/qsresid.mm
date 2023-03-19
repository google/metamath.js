include "cv.mm"
include "cres.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cqs.mm"
include "wcel.mm"
include "ecres2.mm"
include "eqeq2d.mm"
include "rexbiia.mm"
include "abbii.mm"
include "df-qs.mm"
include "3eqtr4i.mm"

theorem qsresid
  let cA: class A
  let cR: class R
  let vu: setvar u
  let vv: setvar v


  assert |- ( A /. ( R |` A ) ) = ( A /. R )

  proof
    vu
    cv
    #
    vv
    cv
    #
    cR
    cA
    cres
    #
    cec
    #
    wceq
    #
    vv
    cA
    wrex
    #
    vu
    cab
    @0
    @1
    cR
    cec
    #
    wceq
    #
    vv
    cA
    wrex
    #
    vu
    cab
    cA
    @2
    cqs
    cA
    cR
    cqs
    @5
    @8
    vu
    @4
    @7
    vv
    cA
    @1
    cA
    wcel
    @3
    @6
    @0
    cA
    @1
    cR
    ecres2
    eqeq2d
    rexbiia
    abbii
    vv
    vu
    cA
    @2
    df-qs
    vv
    vu
    cA
    cR
    df-qs
    3eqtr4i
end
