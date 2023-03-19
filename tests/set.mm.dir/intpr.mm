include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wceq.mm"
include "19.26.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "imbi1i.mm"
include "jaob.mm"
include "bitri.mm"
include "albii.mm"
include "clel4.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "elint.mm"
include "elin.mm"
include "eqriv.mm"

theorem intpr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume intpr.1: |- A e. _V
  assume intpr.2: |- B e. _V


  assert |- |^| { A , B } = ( A i^i B )

  proof
    vx
    cA
    cB
    cpr
    #
    cint
    #
    cA
    cB
    cin
    #
    vy
    cv
    #
    @0
    wcel
    #
    vx
    cv
    #
    @3
    wcel
    #
    wi
    #
    vy
    wal
    #
    @5
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    @5
    @2
    wcel
    @3
    cA
    wceq
    #
    @6
    wi
    #
    @3
    cB
    wceq
    #
    @6
    wi
    #
    wa
    #
    vy
    wal
    @13
    vy
    wal
    #
    @15
    vy
    wal
    #
    wa
    @8
    @11
    @13
    @15
    vy
    19.26
    @7
    @16
    vy
    @7
    @12
    @14
    wo
    #
    @6
    wi
    @16
    @4
    @19
    @6
    @3
    cA
    cB
    vy
    vex
    elpr
    imbi1i
    @12
    @6
    @14
    jaob
    bitri
    albii
    @9
    @17
    @10
    @18
    vy
    @5
    cA
    intpr.1
    clel4
    vy
    @5
    cB
    intpr.2
    clel4
    anbi12i
    3bitr4i
    vy
    @5
    @0
    vx
    vex
    elint
    @5
    cA
    cB
    elin
    3bitr4i
    eqriv
end
