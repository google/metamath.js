include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "cfn.mm"
include "cuni.mm"
include "wral.mm"
include "cptfin.mm"
include "wceq.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "rabeq.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "df-ptfin.mm"
include "elab2g.mm"

theorem isptfin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cX: class X
  let va: setvar a
  assume isptfin.1: |- X = U. A

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint X x
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint B a
  disjoint X a
  assert |- ( A e. B -> ( A e. PtFin <-> A. x e. X { y e. A | x e. y } e. Fin ) )

  proof
    vx
    cv
    vy
    cv
    wcel
    #
    vy
    va
    cv
    #
    crab
    #
    cfn
    wcel
    #
    vx
    @1
    cuni
    #
    wral
    @0
    vy
    cA
    crab
    #
    cfn
    wcel
    #
    vx
    cX
    wral
    va
    cA
    cptfin
    cB
    @1
    cA
    wceq
    #
    @3
    @6
    vx
    @4
    cX
    @7
    @4
    cA
    cuni
    cX
    @1
    cA
    unieq
    isptfin.1
    syl6eqr
    @7
    @2
    @5
    cfn
    @0
    vy
    @1
    cA
    rabeq
    eleq1d
    raleqbidv
    va
    vx
    vy
    df-ptfin
    elab2g
end
