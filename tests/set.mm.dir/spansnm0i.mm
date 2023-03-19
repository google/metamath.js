include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "cin.mm"
include "c0h.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "c0v.mm"
include "chil.mm"
include "csh.mm"
include "wi.mm"
include "spansnchi.mm"
include "chshii.mm"
include "elspansn5.mm"
include "ax-mp.mm"
include "mpanl1.mm"
include "ex.mm"
include "elin.mm"
include "elch0.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "chincli.mm"
include "chle0i.mm"
include "sylib.mm"

theorem spansnm0i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume spansnm0.1: |- A e. ~H
  assume spansnm0.2: |- B e. ~H


  assert |- ( -. A e. ( span ` { B } ) -> ( ( span ` { A } ) i^i ( span ` { B } ) ) = 0H )

  proof
    cA
    cB
    csn
    cspn
    cfv
    #
    wcel
    wn
    #
    cA
    csn
    cspn
    cfv
    #
    @0
    cin
    #
    c0h
    wss
    @3
    c0h
    wceq
    @1
    vx
    @3
    c0h
    @1
    vx
    cv
    #
    @2
    wcel
    @4
    @0
    wcel
    wa
    #
    @4
    c0v
    wceq
    #
    @4
    @3
    wcel
    @4
    c0h
    wcel
    @1
    @5
    @6
    cA
    chil
    wcel
    #
    @1
    @5
    @6
    spansnm0.1
    @0
    csh
    wcel
    @7
    @1
    wa
    @5
    wa
    @6
    wi
    @0
    cB
    spansnm0.2
    spansnchi
    #
    chshii
    @0
    cA
    @4
    elspansn5
    ax-mp
    mpanl1
    ex
    @4
    @2
    @0
    elin
    @4
    elch0
    3imtr4g
    ssrdv
    @3
    @2
    @0
    cA
    spansnm0.1
    spansnchi
    @8
    chincli
    chle0i
    sylib
end
