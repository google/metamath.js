include "weu.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "crn.mm"
include "cvv.mm"
include "wrex.mm"
include "wex.mm"
include "cdm.mm"
include "wfun.mm"
include "crab.mm"
include "wceq.mm"
include "euex.mm"
include "ralimi.mm"
include "rabid2.mm"
include "sylibr.mm"
include "cab.mm"
include "19.42v.mm"
include "abbii.mm"
include "dmopab.mm"
include "df-rab.mm"
include "3eqtr4i.mm"
include "syl6reqr.mm"
include "vex.mm"
include "syl6eqel.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "eumo.mm"
include "imim2i.mm"
include "moanimv.mm"
include "alimi.mm"
include "df-ral.mm"
include "funopab.mm"
include "3imtr4i.mm"
include "funrnex.mm"
include "sylc.mm"
include "nfra1.mm"
include "eleq2d.mm"
include "cop.mm"
include "opabid.mm"
include "opelrn.mm"
include "sylbir.mm"
include "ex.mm"
include "impac.mm"
include "eximi.mm"
include "abeq2i.mm"
include "df-rex.mm"
include "syl6bir.mm"
include "ralrimi.mm"
include "nfopab1.mm"
include "nfrn.mm"
include "nfeq2.mm"
include "nfcv.mm"
include "nfopab2.mm"
include "rexeqf.mm"
include "ralbid.mm"
include "spcegv.mm"

theorem zfrep6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- ( A. x e. z E! y ph -> E. w A. x e. z E. y e. w ph )

  proof
    wph
    vy
    weu
    #
    vx
    vz
    cv
    #
    wral
    #
    vx
    cv
    #
    @1
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    crn
    #
    cvv
    wcel
    #
    wph
    vy
    @7
    wrex
    #
    vx
    @1
    wral
    #
    wph
    vy
    vw
    cv
    #
    wrex
    #
    vx
    @1
    wral
    #
    vw
    wex
    @2
    @6
    cdm
    #
    cvv
    wcel
    @6
    wfun
    #
    @8
    @2
    @14
    @1
    cvv
    @2
    @1
    wph
    vy
    wex
    #
    vx
    @1
    crab
    #
    @14
    @2
    @16
    vx
    @1
    wral
    @1
    @17
    wceq
    @0
    @16
    vx
    @1
    wph
    vy
    euex
    ralimi
    @16
    vx
    @1
    rabid2
    sylibr
    @5
    vy
    wex
    #
    vx
    cab
    @4
    @16
    wa
    #
    vx
    cab
    @14
    @17
    @18
    @19
    vx
    @4
    wph
    vy
    19.42v
    abbii
    @5
    vx
    vy
    dmopab
    #
    @16
    vx
    @1
    df-rab
    3eqtr4i
    syl6reqr
    #
    vz
    vex
    syl6eqel
    @4
    @0
    wi
    #
    vx
    wal
    @5
    vy
    wmo
    #
    vx
    wal
    @2
    @15
    @22
    @23
    vx
    @22
    @4
    wph
    vy
    wmo
    #
    wi
    @23
    @0
    @24
    @4
    wph
    vy
    eumo
    imim2i
    @4
    wph
    vy
    moanimv
    sylibr
    alimi
    @0
    vx
    @1
    df-ral
    @5
    vx
    vy
    funopab
    3imtr4i
    cvv
    @6
    funrnex
    sylc
    @2
    @9
    vx
    @1
    @0
    vx
    @1
    nfra1
    @2
    @4
    @3
    @14
    wcel
    #
    @9
    @2
    @14
    @1
    @3
    @21
    eleq2d
    @18
    vy
    cv
    #
    @7
    wcel
    #
    wph
    wa
    #
    vy
    wex
    @25
    @9
    @5
    @28
    vy
    @4
    wph
    @27
    @4
    wph
    @27
    @5
    @3
    @26
    cop
    @6
    wcel
    @27
    @5
    vx
    vy
    opabid
    @3
    @26
    @6
    vx
    vex
    vy
    vex
    opelrn
    sylbir
    ex
    impac
    eximi
    @18
    vx
    @14
    @20
    abeq2i
    wph
    vy
    @7
    df-rex
    3imtr4i
    syl6bir
    ralrimi
    @13
    @10
    vw
    @7
    cvv
    @11
    @7
    wceq
    @12
    @9
    vx
    @1
    vx
    @11
    @7
    vx
    @6
    @5
    vx
    vy
    nfopab1
    nfrn
    nfeq2
    wph
    vy
    @11
    @7
    vy
    @11
    nfcv
    vy
    @6
    @5
    vx
    vy
    nfopab2
    nfrn
    rexeqf
    ralbid
    spcegv
    sylc
end
