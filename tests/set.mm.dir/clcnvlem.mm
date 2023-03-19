include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "ccnv.mm"
include "wceq.mm"
include "wex.mm"
include "cvv.mm"
include "cxp.mm"
include "cpw.mm"
include "crab.mm"
include "jca.mm"
include "cleq2lem.mm"
include "elabd.mm"
include "cnvintabd.mm"
include "wcel.mm"
include "df-rab.mm"
include "wrel.mm"
include "exsimpl.mm"
include "relcnv.mm"
include "releq.mm"
include "mpbiri.mm"
include "exlimiv.mm"
include "syl.mm"
include "df-rel.mm"
include "sylib.mm"
include "selpw.mm"
include "bicomi.mm"
include "pm4.71ri.mm"
include "abbii.mm"
include "eqtri.mm"
include "inteqi.mm"
include "a1i.mm"
include "vex.mm"
include "cnvex.mm"
include "cdif.mm"
include "cun.mm"
include "ssexd.mm"
include "difexg.mm"
include "unexg.mm"
include "sylancr.mm"
include "wi.mm"
include "cin.mm"
include "inundif.mm"
include "cnvun.mm"
include "sseq1i.mm"
include "biimpi.mm"
include "unssad.mm"
include "relin2.mm"
include "ax-mp.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "cnvss.mm"
include "syl5eqssr.mm"
include "ssid.mm"
include "unss12.mm"
include "sylancl.mm"
include "cnveq.mm"
include "sseq1d.mm"
include "sseq1.mm"
include "3imtr3d.mm"
include "sseq2.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "anim12d.mm"
include "c0.mm"
include "cnvnonrel.mm"
include "0ss.mm"
include "eqsstri.mm"
include "ssequn2.mm"
include "eqtr2i.mm"
include "syl6reqr.mm"
include "jctild.mm"
include "spcimedv.mm"
include "imp.mm"
include "adantlr.mm"
include "wb.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "ex.mm"
include "cnvcnvss.mm"
include "intabssd.mm"
include "weq.mm"
include "eqtr.mm"
include "syl5.mm"
include "impl.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "eqssd.mm"
include "3eqtrd.mm"

theorem clcnvlem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cX: class X
  let vz: setvar z
  assume clcnvlem.sub1: |- ( ( ph /\ x = ( `' y u. ( X \ `' `' X ) ) ) -> ( ch -> ps ) )
  assume clcnvlem.sub2: |- ( ( ph /\ y = `' x ) -> ( ps -> ch ) )
  assume clcnvlem.sub3: |- ( x = A -> ( ps <-> th ) )
  assume clcnvlem.ssub: |- ( ph -> X C_ A )
  assume clcnvlem.ubex: |- ( ph -> A e. _V )
  assume clcnvlem.clex: |- ( ph -> th )

  disjoint A x
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  disjoint th x
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint ph z
  disjoint ps z
  disjoint ch z
  assert |- ( ph -> `' |^| { x | ( X C_ x /\ ps ) } = |^| { y | ( `' X C_ y /\ ch ) } )

  proof
    wph
    cX
    vx
    cv
    #
    wss
    #
    wps
    wa
    #
    vx
    cab
    cint
    ccnv
    vz
    cv
    #
    @0
    ccnv
    #
    wceq
    #
    @2
    wa
    #
    vx
    wex
    #
    vz
    cvv
    cvv
    cxp
    #
    cpw
    #
    crab
    #
    cint
    #
    @7
    vz
    cab
    #
    cint
    #
    cX
    ccnv
    #
    vy
    cv
    #
    wss
    #
    wch
    wa
    #
    vy
    cab
    cint
    #
    wph
    @2
    vx
    vz
    wph
    @2
    cX
    cA
    wss
    #
    wth
    wa
    vx
    cA
    clcnvlem.ubex
    wph
    @19
    wth
    clcnvlem.ssub
    clcnvlem.clex
    jca
    wps
    wth
    @0
    cA
    cX
    clcnvlem.sub3
    cleq2lem
    elabd
    cnvintabd
    @11
    @13
    wceq
    wph
    @10
    @12
    @10
    @3
    @9
    wcel
    #
    @7
    wa
    #
    vz
    cab
    @12
    @7
    vz
    @9
    df-rab
    @21
    @7
    vz
    @7
    @21
    @7
    @20
    @7
    @3
    @8
    wss
    #
    @20
    @7
    @3
    wrel
    #
    @22
    @7
    @5
    vx
    wex
    @23
    @5
    @2
    vx
    exsimpl
    @5
    @23
    vx
    @5
    @23
    @4
    wrel
    @0
    relcnv
    @3
    @4
    releq
    mpbiri
    exlimiv
    syl
    @3
    df-rel
    sylib
    @20
    @22
    vz
    @8
    selpw
    bicomi
    sylib
    pm4.71ri
    bicomi
    abbii
    eqtri
    inteqi
    a1i
    wph
    @13
    @18
    wph
    @7
    @17
    vz
    vy
    @15
    ccnv
    #
    ccnv
    #
    cvv
    @25
    cvv
    wcel
    wph
    @24
    @15
    vy
    vex
    cnvex
    #
    cnvex
    a1i
    wph
    @3
    @25
    wceq
    #
    wa
    #
    @17
    @7
    @28
    @17
    wa
    @7
    @25
    @4
    wceq
    #
    @2
    wa
    #
    vx
    wex
    #
    wph
    @17
    @31
    @27
    wph
    @17
    @31
    wph
    @30
    @17
    vx
    @24
    cX
    @14
    ccnv
    #
    cdif
    #
    cun
    #
    cvv
    wph
    @24
    cvv
    wcel
    @33
    cvv
    wcel
    #
    @34
    cvv
    wcel
    @26
    wph
    cX
    cvv
    wcel
    @35
    wph
    cX
    cA
    cvv
    clcnvlem.ubex
    clcnvlem.ssub
    ssexd
    cX
    @32
    cvv
    difexg
    syl
    @24
    @33
    cvv
    cvv
    unexg
    sylancr
    wph
    @0
    @34
    wceq
    #
    wa
    #
    @17
    @2
    @29
    @37
    @16
    @1
    wch
    wps
    @36
    @16
    @1
    wi
    wph
    @16
    @1
    @36
    cX
    @34
    wss
    #
    cX
    @32
    cin
    #
    @33
    cun
    #
    cX
    wceq
    #
    @16
    @38
    wi
    cX
    @32
    inundif
    @41
    @40
    ccnv
    #
    @15
    wss
    #
    @40
    @34
    wss
    #
    @16
    @38
    @43
    @44
    wi
    @41
    @43
    @39
    @24
    wss
    #
    @33
    @33
    wss
    @44
    @43
    @39
    ccnv
    #
    @15
    wss
    #
    @45
    @43
    @46
    @33
    ccnv
    #
    @15
    @43
    @46
    @48
    cun
    #
    @15
    wss
    @42
    @49
    @15
    @39
    @33
    cnvun
    sseq1i
    biimpi
    unssad
    @47
    @39
    @46
    ccnv
    #
    @24
    @39
    wrel
    #
    @50
    @39
    wceq
    @32
    wrel
    @51
    @14
    relcnv
    cX
    @32
    relin2
    ax-mp
    @39
    dfrel2
    mpbi
    @46
    @15
    cnvss
    syl5eqssr
    syl
    @33
    ssid
    @39
    @24
    @33
    @33
    unss12
    sylancl
    a1i
    @41
    @42
    @14
    @15
    @40
    cX
    cnveq
    sseq1d
    @40
    cX
    @34
    sseq1
    3imtr3d
    ax-mp
    @0
    @34
    cX
    sseq2
    syl5ibr
    adantl
    clcnvlem.sub1
    anim12d
    @36
    @29
    wph
    @36
    @4
    @34
    ccnv
    #
    @25
    @0
    @34
    cnveq
    @52
    @25
    @48
    cun
    #
    @25
    @24
    @33
    cnvun
    @48
    @25
    wss
    @53
    @25
    wceq
    @48
    c0
    @25
    cX
    cnvnonrel
    @25
    0ss
    eqsstri
    @48
    @25
    ssequn2
    mpbi
    eqtr2i
    syl6reqr
    adantl
    jctild
    spcimedv
    imp
    adantlr
    @27
    @7
    @31
    wb
    wph
    @17
    @27
    @6
    @30
    vx
    @27
    @5
    @29
    @2
    @3
    @25
    @4
    eqeq1
    anbi1d
    exbidv
    ad2antlr
    mpbird
    ex
    @25
    @15
    wss
    wph
    @15
    cnvcnvss
    a1i
    intabssd
    wph
    @17
    @7
    vy
    vz
    @3
    cvv
    @3
    cvv
    wcel
    wph
    vz
    vex
    a1i
    wph
    vy
    vz
    weq
    #
    wa
    #
    @6
    @17
    vx
    @55
    @5
    @2
    @17
    wph
    @54
    @5
    @2
    @17
    wi
    #
    @54
    @5
    wa
    @15
    @4
    wceq
    #
    wph
    @56
    @15
    @3
    @4
    eqtr
    wph
    @57
    @56
    wph
    @57
    wa
    @1
    @16
    wps
    wch
    @57
    @1
    @16
    wi
    wph
    @1
    @16
    @57
    @14
    @4
    wss
    cX
    @0
    cnvss
    @15
    @4
    @14
    sseq2
    syl5ibr
    adantl
    clcnvlem.sub2
    anim12d
    ex
    syl5
    impl
    expimpd
    exlimdv
    @3
    @3
    wss
    wph
    @3
    ssid
    a1i
    intabssd
    eqssd
    3eqtrd
end
