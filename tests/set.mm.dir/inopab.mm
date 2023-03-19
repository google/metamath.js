include "copab.mm"
include "cin.mm"
include "wa.mm"
include "wrel.mm"
include "relopab.mm"
include "relin1.mm"
include "ax-mp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wsb.mm"
include "sban.mm"
include "sbbii.mm"
include "opelopabsbALT.mm"
include "anbi12i.mm"
include "3bitr4ri.mm"
include "elin.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem inopab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph z
  disjoint ph w
  disjoint ps z
  disjoint ps w
  assert |- ( { <. x , y >. | ph } i^i { <. x , y >. | ps } ) = { <. x , y >. | ( ph /\ ps ) }

  proof
    vz
    vw
    wph
    vx
    vy
    copab
    #
    wps
    vx
    vy
    copab
    #
    cin
    #
    wph
    wps
    wa
    #
    vx
    vy
    copab
    #
    @0
    wrel
    @2
    wrel
    wph
    vx
    vy
    relopab
    @0
    @1
    relin1
    ax-mp
    @3
    vx
    vy
    relopab
    vz
    cv
    vw
    cv
    cop
    #
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wa
    #
    @3
    vx
    vz
    wsb
    #
    vy
    vw
    wsb
    #
    @5
    @2
    wcel
    @5
    @4
    wcel
    wph
    vx
    vz
    wsb
    #
    wps
    vx
    vz
    wsb
    #
    wa
    #
    vy
    vw
    wsb
    @11
    vy
    vw
    wsb
    #
    @12
    vy
    vw
    wsb
    #
    wa
    @10
    @8
    @11
    @12
    vy
    vw
    sban
    @9
    @13
    vy
    vw
    wph
    wps
    vx
    vz
    sban
    sbbii
    @6
    @14
    @7
    @15
    wph
    vx
    vy
    vz
    vw
    opelopabsbALT
    wps
    vx
    vy
    vz
    vw
    opelopabsbALT
    anbi12i
    3bitr4ri
    @5
    @0
    @1
    elin
    @3
    vx
    vy
    vz
    vw
    opelopabsbALT
    3bitr4i
    eqrelriiv
end
