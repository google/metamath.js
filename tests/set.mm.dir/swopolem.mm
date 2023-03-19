include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "ralrimivvva.mm"
include "wceq.mm"
include "breq1.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "orbi2d.mm"
include "orbi12d.mm"
include "imbi2d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem swopolem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume swopolem.1: |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( x R y -> ( x R z \/ z R y ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  disjoint Z z
  assert |- ( ( ph /\ ( X e. A /\ Y e. A /\ Z e. A ) ) -> ( X R Y -> ( X R Z \/ Z R Y ) ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @0
    vz
    cv
    #
    cR
    wbr
    #
    @3
    @1
    cR
    wbr
    #
    wo
    #
    wi
    #
    vz
    cA
    wral
    vy
    cA
    wral
    vx
    cA
    wral
    cX
    cA
    wcel
    cY
    cA
    wcel
    cZ
    cA
    wcel
    w3a
    cX
    cY
    cR
    wbr
    #
    cX
    cZ
    cR
    wbr
    #
    cZ
    cY
    cR
    wbr
    #
    wo
    #
    wi
    #
    wph
    @7
    vx
    vy
    vz
    cA
    cA
    cA
    swopolem.1
    ralrimivvva
    @7
    @12
    cX
    @1
    cR
    wbr
    #
    cX
    @3
    cR
    wbr
    #
    @5
    wo
    #
    wi
    @8
    @14
    @3
    cY
    cR
    wbr
    #
    wo
    #
    wi
    vx
    vy
    vz
    cX
    cY
    cZ
    cA
    cA
    cA
    @0
    cX
    wceq
    #
    @2
    @13
    @6
    @15
    @0
    cX
    @1
    cR
    breq1
    @18
    @4
    @14
    @5
    @0
    cX
    @3
    cR
    breq1
    orbi1d
    imbi12d
    @1
    cY
    wceq
    #
    @13
    @8
    @15
    @17
    @1
    cY
    cX
    cR
    breq2
    @19
    @5
    @16
    @14
    @1
    cY
    @3
    cR
    breq2
    orbi2d
    imbi12d
    @3
    cZ
    wceq
    #
    @17
    @11
    @8
    @20
    @14
    @9
    @16
    @10
    @3
    cZ
    cX
    cR
    breq2
    @3
    cZ
    cY
    cR
    breq1
    orbi12d
    imbi2d
    rspc3v
    mpan9
end
