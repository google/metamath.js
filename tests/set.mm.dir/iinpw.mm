include "cint.mm"
include "cpw.mm"
include "cv.mm"
include "ciin.mm"
include "wss.mm"
include "wcel.mm"
include "wral.mm"
include "ssint.mm"
include "selpw.mm"
include "ralbii.mm"
include "bitr4i.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iinpw
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ~P |^| A = |^|_ x e. A ~P x

  proof
    vy
    cA
    cint
    #
    cpw
    #
    vx
    cA
    vx
    cv
    #
    cpw
    #
    ciin
    #
    vy
    cv
    #
    @0
    wss
    #
    @5
    @3
    wcel
    #
    vx
    cA
    wral
    #
    @5
    @1
    wcel
    @5
    @4
    wcel
    #
    @6
    @5
    @2
    wss
    #
    vx
    cA
    wral
    @8
    vx
    @5
    cA
    ssint
    @7
    @10
    vx
    cA
    vy
    @2
    selpw
    ralbii
    bitr4i
    vy
    @0
    selpw
    @5
    cvv
    wcel
    @9
    @8
    wb
    vy
    vex
    vx
    @5
    cA
    @3
    cvv
    eliin
    ax-mp
    3bitr4i
    eqriv
end
