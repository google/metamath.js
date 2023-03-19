include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "weq.mm"
include "wo.mm"
include "equid.mm"
include "orci.mm"
include "wb.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "equequ2.mm"
include "breq1.mm"
include "orbi12d.mm"
include "breq2.mm"
include "notbid.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "con2bid.mm"
include "chvarv.mm"
include "mpbii.mm"
include "anidms.mm"
include "w3o.mm"
include "biimprd.mm"
include "orrd.mm"
include "3orass.mm"
include "sylibr.mm"
include "issoi.mm"

theorem isso2i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume isso2i.1: |- ( ( x e. A /\ y e. A ) -> ( x R y <-> -. ( x = y \/ y R x ) ) )
  assume isso2i.2: |- ( ( x e. A /\ y e. A /\ z e. A ) -> ( ( x R y /\ y R z ) -> x R z ) )

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- R Or A

  proof
    vx
    vy
    vz
    cA
    cR
    vx
    cv
    #
    cA
    wcel
    #
    @0
    @0
    cR
    wbr
    #
    wn
    #
    @1
    @1
    wa
    #
    vx
    vx
    weq
    #
    @2
    wo
    #
    @3
    @5
    @2
    vx
    equid
    orci
    @1
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    vx
    vy
    weq
    #
    @7
    @0
    cR
    wbr
    #
    wo
    #
    @0
    @7
    cR
    wbr
    #
    wn
    #
    wb
    #
    wi
    @4
    @6
    @3
    wb
    #
    wi
    vy
    vx
    vy
    vx
    weq
    #
    @9
    @4
    @15
    @16
    @17
    @8
    @1
    @1
    @7
    @0
    cA
    eleq1
    anbi2d
    @17
    @12
    @6
    @14
    @3
    @17
    @10
    @5
    @11
    @2
    vy
    vx
    vx
    equequ2
    @7
    @0
    @0
    cR
    breq1
    orbi12d
    @17
    @13
    @2
    @7
    @0
    @0
    cR
    breq2
    notbid
    bibi12d
    imbi12d
    @9
    @13
    @12
    isso2i.1
    con2bid
    #
    chvarv
    mpbii
    anidms
    isso2i.2
    @9
    @13
    @12
    wo
    @13
    @10
    @11
    w3o
    @9
    @13
    @12
    @9
    @12
    @14
    @18
    biimprd
    orrd
    @13
    @10
    @11
    3orass
    sylibr
    issoi
end
