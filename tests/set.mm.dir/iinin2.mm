include "c0.mm"
include "wne.mm"
include "cin.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "r19.28zv.mm"
include "elin.mm"
include "ralbii.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "anbi2i.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem iinin2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A =/= (/) -> |^|_ x e. A ( B i^i C ) = ( B i^i |^|_ x e. A C ) )

  proof
    cA
    c0
    wne
    #
    vy
    vx
    cA
    cB
    cC
    cin
    #
    ciin
    #
    cB
    vx
    cA
    cC
    ciin
    #
    cin
    #
    @0
    vy
    cv
    #
    @1
    wcel
    #
    vx
    cA
    wral
    #
    @5
    cB
    wcel
    #
    @5
    @3
    wcel
    #
    wa
    #
    @5
    @2
    wcel
    #
    @5
    @4
    wcel
    @0
    @8
    @5
    cC
    wcel
    #
    wa
    #
    vx
    cA
    wral
    @8
    @12
    vx
    cA
    wral
    #
    wa
    @7
    @10
    @8
    @12
    vx
    cA
    r19.28zv
    @6
    @13
    vx
    cA
    @5
    cB
    cC
    elin
    ralbii
    @9
    @14
    @8
    @5
    cvv
    wcel
    #
    @9
    @14
    wb
    vy
    vex
    #
    vx
    @5
    cA
    cC
    cvv
    eliin
    ax-mp
    anbi2i
    3bitr4g
    @15
    @11
    @7
    wb
    @16
    vx
    @5
    cA
    @1
    cvv
    eliin
    ax-mp
    @5
    cB
    @3
    elin
    3bitr4g
    eqrdv
end
