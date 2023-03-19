include "crn.mm"
include "cdm.mm"
include "cin.mm"
include "incom.mm"
include "eqsstr3i.mm"
include "cotr2g.mm"

theorem cotr2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume cotr2.a: |- dom R C_ A
  assume cotr2.b: |- ( dom R i^i ran R ) C_ B
  assume cotr2.c: |- ran R C_ C

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  assert |- ( ( R o. R ) C_ R <-> A. x e. A A. y e. B A. z e. C ( ( x R y /\ y R z ) -> x R z ) )

  proof
    vx
    vy
    vz
    cR
    cR
    cR
    cA
    cB
    cC
    cotr2.a
    cR
    crn
    #
    cR
    cdm
    #
    cin
    @1
    @0
    cin
    cB
    @1
    @0
    incom
    cotr2.b
    eqsstr3i
    cotr2.c
    cotr2g
end
