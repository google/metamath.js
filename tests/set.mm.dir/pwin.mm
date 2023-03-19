include "cpw.mm"
include "cin.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "ssin.mm"
include "selpw.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "ineqri.mm"
include "eqcomi.mm"

theorem pwin
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ~P ( A i^i B ) = ( ~P A i^i ~P B )

  proof
    cA
    cpw
    #
    cB
    cpw
    #
    cin
    cA
    cB
    cin
    #
    cpw
    #
    vx
    @0
    @1
    @3
    vx
    cv
    #
    cA
    wss
    #
    @4
    cB
    wss
    #
    wa
    @4
    @2
    wss
    @4
    @0
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    @4
    @3
    wcel
    @4
    cA
    cB
    ssin
    @7
    @5
    @8
    @6
    vx
    cA
    selpw
    vx
    cB
    selpw
    anbi12i
    vx
    @2
    selpw
    3bitr4i
    ineqri
    eqcomi
end
