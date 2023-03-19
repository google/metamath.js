include "cv.mm"
include "wor.mm"
include "wel.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "crpss.mm"
include "wss.mm"
include "wne.mm"
include "wi.mm"
include "w3a.mm"
include "ancom.mm"
include "3anass.mm"
include "bitr4i.mm"
include "sotr.mm"
include "sylan2b.mm"
include "anassrs.mm"
include "ancomsd.mm"
include "expdimp.mm"
include "an32s.mm"
include "ss2rabdv.mm"
include "wcel.mm"
include "wn.mm"
include "breq1.mm"
include "elrab.mm"
include "biimpri.mm"
include "adantll.mm"
include "sonr.mm"
include "simprbi.mm"
include "nsyl.mm"
include "adantr.mm"
include "nelne1.mm"
include "necomd.mm"
include "syl2anc.mm"
include "adantlrr.mm"
include "wpss.mm"
include "vex.mm"
include "rabex.mm"
include "brrpss.mm"
include "df-pss.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "ex.mm"

theorem fin2solem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cR: class R
  let vu: setvar u
  let vv: setvar v
  let cA: class A

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint R u
  disjoint R v
  assert |- ( ( R Or x /\ ( y e. x /\ z e. x ) ) -> ( y R z -> { w e. x | w R y } [C.] { w e. x | w R z } ) )

  proof
    vx
    cv
    #
    cR
    wor
    #
    vy
    vx
    wel
    #
    vz
    vx
    wel
    #
    wa
    #
    wa
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    vw
    cv
    #
    @6
    cR
    wbr
    #
    vw
    @0
    crab
    #
    @9
    @7
    cR
    wbr
    #
    vw
    @0
    crab
    #
    crpss
    wbr
    #
    @5
    @8
    wa
    #
    @11
    @13
    wss
    #
    @11
    @13
    wne
    #
    @14
    @15
    @10
    @12
    vw
    @0
    @5
    vw
    vx
    wel
    #
    @8
    @10
    @12
    wi
    @5
    @18
    wa
    #
    @8
    @10
    @12
    @19
    @10
    @8
    @12
    @1
    @4
    @18
    @10
    @8
    wa
    @12
    wi
    #
    @4
    @18
    wa
    #
    @1
    @18
    @2
    @3
    w3a
    #
    @20
    @21
    @18
    @4
    wa
    @22
    @4
    @18
    ancom
    @18
    @2
    @3
    3anass
    bitr4i
    @0
    @9
    @6
    @7
    cR
    sotr
    sylan2b
    anassrs
    ancomsd
    expdimp
    an32s
    ss2rabdv
    @1
    @2
    @8
    @17
    @3
    @1
    @2
    wa
    #
    @8
    wa
    @6
    @13
    wcel
    #
    @6
    @11
    wcel
    #
    wn
    #
    @17
    @2
    @8
    @24
    @1
    @24
    @2
    @8
    wa
    @12
    @8
    vw
    @6
    @0
    @9
    @6
    @7
    cR
    breq1
    elrab
    biimpri
    adantll
    @23
    @26
    @8
    @23
    @6
    @6
    cR
    wbr
    #
    @25
    @0
    @6
    cR
    sonr
    @25
    @2
    @27
    @10
    @27
    vw
    @6
    @0
    @9
    @6
    @6
    cR
    breq1
    elrab
    simprbi
    nsyl
    adantr
    @24
    @26
    wa
    @13
    @11
    @6
    @13
    @11
    nelne1
    necomd
    syl2anc
    adantlrr
    @14
    @11
    @13
    wpss
    @16
    @17
    wa
    @11
    @13
    @12
    vw
    @0
    vx
    vex
    rabex
    brrpss
    @11
    @13
    df-pss
    bitri
    sylanbrc
    ex
end
