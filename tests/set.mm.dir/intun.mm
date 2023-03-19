include "cun.mm"
include "cint.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "19.26.mm"
include "wo.mm"
include "elun.mm"
include "imbi1i.mm"
include "jaob.mm"
include "bitri.mm"
include "albii.mm"
include "vex.mm"
include "elint.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "elin.mm"
include "eqriv.mm"

theorem intun
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- |^| ( A u. B ) = ( |^| A i^i |^| B )

  proof
    vx
    cA
    cB
    cun
    #
    cint
    #
    cA
    cint
    #
    cB
    cint
    #
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
    @5
    wcel
    #
    wi
    #
    vy
    wal
    #
    @7
    @2
    wcel
    #
    @7
    @3
    wcel
    #
    wa
    #
    @7
    @1
    wcel
    @7
    @4
    wcel
    @5
    cA
    wcel
    #
    @8
    wi
    #
    @5
    cB
    wcel
    #
    @8
    wi
    #
    wa
    #
    vy
    wal
    @15
    vy
    wal
    #
    @17
    vy
    wal
    #
    wa
    @10
    @13
    @15
    @17
    vy
    19.26
    @9
    @18
    vy
    @9
    @14
    @16
    wo
    #
    @8
    wi
    @18
    @6
    @21
    @8
    @5
    cA
    cB
    elun
    imbi1i
    @14
    @8
    @16
    jaob
    bitri
    albii
    @11
    @19
    @12
    @20
    vy
    @7
    cA
    vx
    vex
    #
    elint
    vy
    @7
    cB
    @22
    elint
    anbi12i
    3bitr4i
    vy
    @7
    @0
    @22
    elint
    @7
    @2
    @3
    elin
    3bitr4i
    eqriv
end
