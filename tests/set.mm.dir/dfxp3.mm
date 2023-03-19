include "cv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "coprab.mm"
include "w3a.mm"
include "cop.mm"
include "wceq.mm"
include "biidd.mm"
include "dfoprab4.mm"
include "df-xp.mm"
include "df-3an.mm"
include "oprabbii.mm"
include "3eqtr4i.mm"

theorem dfxp3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint B u
  disjoint C u
  assert |- ( ( A X. B ) X. C ) = { <. <. x , y >. , z >. | ( x e. A /\ y e. B /\ z e. C ) }

  proof
    vu
    cv
    #
    cA
    cB
    cxp
    #
    wcel
    vz
    cv
    cC
    wcel
    #
    wa
    vu
    vz
    copab
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    @2
    wa
    #
    vx
    vy
    vz
    coprab
    @1
    cC
    cxp
    @4
    @6
    @2
    w3a
    #
    vx
    vy
    vz
    coprab
    @2
    @2
    vx
    vy
    vz
    vu
    cA
    cB
    @0
    @3
    @5
    cop
    wceq
    @2
    biidd
    dfoprab4
    vu
    vz
    @1
    cC
    df-xp
    @8
    @7
    vx
    vy
    vz
    @4
    @6
    @2
    df-3an
    oprabbii
    3eqtr4i
end
