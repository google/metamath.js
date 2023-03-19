include "cima.mm"
include "wss.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cxp.mm"
include "cin.mm"
include "cqs.mm"
include "wcel.mm"
include "wa.mm"
include "ecinxp.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "abbidv.mm"
include "df-qs.mm"
include "3eqtr4g.mm"

theorem qsinxp
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let wph: wff ph


  assert |- ( ( R " A ) C_ A -> ( A /. R ) = ( A /. ( R i^i ( A X. A ) ) ) )

  proof
    cR
    cA
    cima
    cA
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    cR
    cec
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @1
    @2
    cR
    cA
    cA
    cxp
    cin
    #
    cec
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    cA
    cR
    cqs
    cA
    @6
    cqs
    @0
    @5
    @9
    vy
    @0
    @4
    @8
    vx
    cA
    @0
    @2
    cA
    wcel
    wa
    @3
    @7
    @1
    cA
    @2
    cR
    ecinxp
    eqeq2d
    rexbidva
    abbidv
    vx
    vy
    cA
    cR
    df-qs
    vx
    vy
    cA
    @6
    df-qs
    3eqtr4g
end
