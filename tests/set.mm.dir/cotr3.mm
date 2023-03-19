include "cdm.mm"
include "eqimss2i.mm"
include "crn.mm"
include "cin.mm"
include "ineq12i.mm"
include "eqtri.mm"
include "cotr2.mm"

theorem cotr3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume cotr3.a: |- A = dom R
  assume cotr3.b: |- B = ( A i^i C )
  assume cotr3.c: |- C = ran R

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
    cA
    cB
    cC
    cR
    cA
    cR
    cdm
    #
    cotr3.a
    eqimss2i
    cB
    @0
    cR
    crn
    #
    cin
    #
    cB
    cA
    cC
    cin
    @2
    cotr3.b
    cA
    @0
    cC
    @1
    cotr3.a
    cotr3.c
    ineq12i
    eqtri
    eqimss2i
    cC
    @1
    cotr3.c
    eqimss2i
    cotr2
end
