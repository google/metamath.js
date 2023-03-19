include "cio.mm"
include "cab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "cuni.mm"
include "csingles.mm"
include "cin.mm"
include "df-iota.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "wb.mm"
include "abeq1.mm"
include "wel.mm"
include "exdistr.mm"
include "weq.mm"
include "vex.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "snex.mm"
include "eqeq1.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "eqcom.mm"
include "velsn.mm"
include "equcom.mm"
include "bitri.mm"
include "anbi12ci.mm"
include "syl6bb.mm"
include "an13.mm"
include "exbii.mm"
include "bitr3i.mm"
include "excom.mm"
include "eluniab.mm"
include "3bitr4i.mm"
include "mpgbir.mm"
include "df-sn.mm"
include "dfsingles2.mm"
include "ineq12i.mm"
include "inab.mm"
include "19.42v.mm"
include "bicomi.mm"
include "abbii.mm"
include "eqtri.mm"
include "unieqi.mm"
include "eqtr4i.mm"

theorem dfiota3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( iota x ph ) = U. U. ( { { x | ph } } i^i Singletons )

  proof
    wph
    vx
    cio
    wph
    vx
    cab
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    cab
    #
    cuni
    @0
    csn
    #
    csingles
    cin
    #
    cuni
    #
    cuni
    wph
    vx
    vy
    df-iota
    @4
    @7
    @4
    vz
    cv
    #
    @0
    wceq
    #
    @8
    vw
    cv
    #
    csn
    #
    wceq
    #
    wa
    #
    vw
    wex
    #
    vz
    cab
    #
    cuni
    #
    @7
    @4
    @16
    wceq
    @3
    @1
    @16
    wcel
    #
    wb
    vy
    @3
    vy
    @16
    abeq1
    vy
    vz
    wel
    #
    @13
    wa
    #
    vw
    wex
    vz
    wex
    #
    @18
    @14
    wa
    vz
    wex
    @3
    @17
    @18
    @13
    vz
    vw
    exdistr
    @3
    @19
    vz
    wex
    #
    vw
    wex
    #
    @20
    @3
    vw
    vy
    weq
    #
    @0
    @11
    wceq
    #
    wa
    #
    vw
    wex
    @22
    @24
    @3
    vw
    @1
    vy
    vex
    @23
    @11
    @2
    @0
    @10
    @1
    sneq
    eqeq2d
    ceqsexv
    @25
    @21
    vw
    @25
    @12
    @9
    @18
    wa
    #
    wa
    #
    vz
    wex
    @21
    @26
    @25
    vz
    @11
    @10
    snex
    @12
    @26
    @11
    @0
    wceq
    #
    @1
    @11
    wcel
    #
    wa
    @25
    @12
    @9
    @28
    @18
    @29
    @8
    @11
    @0
    eqeq1
    @8
    @11
    @1
    eleq2
    anbi12d
    @28
    @24
    @29
    @23
    @11
    @0
    eqcom
    @29
    vy
    vw
    weq
    @23
    vy
    @10
    velsn
    vy
    vw
    equcom
    bitri
    anbi12ci
    syl6bb
    ceqsexv
    @27
    @19
    vz
    @12
    @9
    @18
    an13
    exbii
    bitr3i
    exbii
    bitr3i
    @19
    vw
    vz
    excom
    bitri
    @14
    vz
    @1
    eluniab
    3bitr4i
    mpgbir
    @6
    @15
    @6
    @9
    vz
    cab
    #
    @12
    vw
    wex
    #
    vz
    cab
    #
    cin
    #
    @15
    @5
    @30
    csingles
    @32
    vz
    @0
    df-sn
    vz
    vw
    dfsingles2
    ineq12i
    @33
    @9
    @31
    wa
    #
    vz
    cab
    @15
    @9
    @31
    vz
    inab
    @34
    @14
    vz
    @14
    @34
    @9
    @12
    vw
    19.42v
    bicomi
    abbii
    eqtri
    eqtri
    unieqi
    eqtr4i
    unieqi
    eqtri
end
