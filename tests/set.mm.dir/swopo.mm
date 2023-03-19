include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "id.mm"
include "ancli.mm"
include "ralrimivva.mm"
include "weq.mm"
include "breq1.mm"
include "breq2.mm"
include "notbid.mm"
include "imbi12d.mm"
include "rspc2va.mm"
include "syl2anr.mm"
include "pm2.01d.mm"
include "w3a.mm"
include "3adantr1.mm"
include "wo.mm"
include "imp.mm"
include "orcomd.mm"
include "ord.mm"
include "expimpd.mm"
include "sylan2d.mm"
include "ispod.mm"

theorem swopo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume swopo.1: |- ( ( ph /\ ( y e. A /\ z e. A ) ) -> ( y R z -> -. z R y ) )
  assume swopo.2: |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( x R y -> ( x R z \/ z R y ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> R Po A )

  proof
    wph
    vx
    vy
    vz
    cA
    cR
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    @0
    @0
    cR
    wbr
    #
    @1
    @1
    @1
    wa
    vy
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    @4
    @3
    cR
    wbr
    #
    wn
    #
    wi
    #
    vz
    cA
    wral
    vy
    cA
    wral
    @2
    @2
    wn
    #
    wi
    #
    wph
    @1
    @1
    @1
    id
    ancli
    wph
    @8
    vy
    vz
    cA
    cA
    swopo.1
    ralrimivva
    @8
    @10
    @0
    @4
    cR
    wbr
    #
    @4
    @0
    cR
    wbr
    #
    wn
    #
    wi
    vy
    vz
    @0
    @0
    cA
    cA
    vy
    vx
    weq
    #
    @5
    @11
    @7
    @13
    @3
    @0
    @4
    cR
    breq1
    @14
    @6
    @12
    @3
    @0
    @4
    cR
    breq2
    notbid
    imbi12d
    vz
    vx
    weq
    #
    @11
    @2
    @13
    @9
    @4
    @0
    @0
    cR
    breq2
    @15
    @12
    @2
    @4
    @0
    @0
    cR
    breq1
    notbid
    imbi12d
    rspc2va
    syl2anr
    pm2.01d
    wph
    @1
    @3
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    w3a
    wa
    #
    @5
    @7
    @0
    @3
    cR
    wbr
    #
    @11
    wph
    @16
    @17
    @8
    @1
    swopo.1
    3adantr1
    @18
    @19
    @7
    @11
    @18
    @19
    wa
    #
    @6
    @11
    @20
    @11
    @6
    @18
    @19
    @11
    @6
    wo
    swopo.2
    imp
    orcomd
    ord
    expimpd
    sylan2d
    ispod
end
