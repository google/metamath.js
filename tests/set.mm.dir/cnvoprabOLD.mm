include "copab.mm"
include "ccnv.mm"
include "coprab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "excom.mm"
include "nfv.mm"
include "nfan.mm"
include "nfex.mm"
include "opex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "exlimi.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "adantl.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wi.mm"
include "fvex.mm"
include "wb.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "eqopi.mm"
include "sylan2br.mm"
include "bicomd.mm"
include "syl.mm"
include "spc2ed.mm"
include "mpanr12.mm"
include "mpcom.mm"
include "exlimiv.mm"
include "impbii.mm"
include "exbii.mm"
include "exrot3.mm"
include "3bitr2ri.mm"
include "abbii.mm"
include "df-oprab.mm"
include "df-opab.mm"
include "3eqtr4ri.mm"
include "cnveqi.mm"
include "cnvopab.mm"
include "eqtr3i.mm"

theorem cnvoprabOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vw: setvar w
  assume cnvoprabOLD.x: |- F/ x ps
  assume cnvoprabOLD.y: |- F/ y ps
  assume cnvoprabOLD.1: |- ( a = <. x , y >. -> ( ps <-> ph ) )
  assume cnvoprabOLD.2: |- ( ps -> a e. ( _V X. _V ) )

  disjoint a x
  disjoint a y
  disjoint a z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a ph
  disjoint a w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint ps w
  assert |- `' { <. <. x , y >. , z >. | ph } = { <. z , a >. | ps }

  proof
    wps
    va
    vz
    copab
    #
    ccnv
    wph
    vx
    vy
    vz
    coprab
    #
    ccnv
    wps
    vz
    va
    copab
    @0
    @1
    vw
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    #
    vw
    cab
    @2
    va
    cv
    #
    @6
    cop
    #
    wceq
    #
    wps
    wa
    #
    vz
    wex
    va
    wex
    #
    vw
    cab
    @1
    @0
    @10
    @15
    vw
    @15
    @14
    va
    wex
    #
    vz
    wex
    @9
    vy
    wex
    #
    vx
    wex
    #
    vz
    wex
    @10
    @14
    va
    vz
    excom
    @18
    @16
    vz
    @18
    @16
    @17
    @16
    vx
    @14
    vx
    va
    @13
    wps
    vx
    @13
    vx
    nfv
    cnvoprabOLD.x
    nfan
    #
    nfex
    @9
    @16
    vy
    @14
    vy
    va
    @13
    wps
    vy
    @13
    vy
    nfv
    cnvoprabOLD.y
    nfan
    #
    nfex
    @14
    @9
    va
    @5
    @3
    @4
    opex
    @11
    @5
    wceq
    #
    @13
    @8
    wps
    wph
    @21
    @12
    @7
    @2
    @11
    @5
    @6
    opeq1
    eqeq2d
    cnvoprabOLD.1
    anbi12d
    #
    spcev
    exlimi
    exlimi
    @14
    @18
    va
    @11
    cvv
    cvv
    cxp
    wcel
    #
    @14
    @18
    wps
    @23
    @13
    cnvoprabOLD.2
    adantl
    @23
    @11
    c1st
    cfv
    #
    cvv
    wcel
    @11
    c2nd
    cfv
    #
    cvv
    wcel
    @14
    @18
    wi
    @11
    c1st
    fvex
    @11
    c2nd
    fvex
    @23
    @9
    @14
    vx
    vy
    @24
    @25
    cvv
    cvv
    @19
    @20
    @23
    @3
    @24
    wceq
    #
    @4
    @25
    wceq
    #
    wa
    #
    wa
    @21
    @9
    @14
    wb
    @28
    @23
    @24
    @3
    wceq
    #
    @25
    @4
    wceq
    #
    wa
    @21
    @29
    @26
    @30
    @27
    @24
    @3
    eqcom
    @25
    @4
    eqcom
    anbi12i
    @11
    @3
    @4
    cvv
    cvv
    eqopi
    sylan2br
    @21
    @14
    @9
    @22
    bicomd
    syl
    spc2ed
    mpanr12
    mpcom
    exlimiv
    impbii
    exbii
    @9
    vz
    vx
    vy
    exrot3
    3bitr2ri
    abbii
    wph
    vx
    vy
    vz
    vw
    df-oprab
    wps
    va
    vz
    vw
    df-opab
    3eqtr4ri
    cnveqi
    wps
    va
    vz
    cnvopab
    eqtr3i
end
