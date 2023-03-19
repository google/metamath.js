include "cep.mm"
include "wwe.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wel.mm"
include "wor.mm"
include "wi.mm"
include "weso.mm"
include "sotr.mm"
include "sylan.mm"
include "epel.mm"
include "anbi12i.mm"
include "3imtr3g.mm"

theorem wetrep
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A


  assert |- ( ( _E We A /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( ( x e. y /\ y e. z ) -> x e. z ) )

  proof
    cA
    cep
    wwe
    #
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cA
    wcel
    vz
    cv
    #
    cA
    wcel
    w3a
    #
    wa
    @1
    @2
    cep
    wbr
    #
    @2
    @3
    cep
    wbr
    #
    wa
    #
    @1
    @3
    cep
    wbr
    #
    vx
    vy
    wel
    #
    vy
    vz
    wel
    #
    wa
    vx
    vz
    wel
    @0
    cA
    cep
    wor
    @4
    @7
    @8
    wi
    cA
    cep
    weso
    cA
    @1
    @2
    @3
    cep
    sotr
    sylan
    @5
    @9
    @6
    @10
    vx
    vy
    epel
    vy
    vz
    epel
    anbi12i
    vx
    vz
    epel
    3imtr3g
end
