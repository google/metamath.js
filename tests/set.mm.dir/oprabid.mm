include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "coprab.mm"
include "opex.mm"
include "wi.mm"
include "vex.mm"
include "eqvinop.mm"
include "biimpi.mm"
include "eqeq1.mm"
include "opth1.mm"
include "syl6bi.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "weq.mm"
include "w3a.mm"
include "otth2.mm"
include "weu.mm"
include "euequ1.mm"
include "eupick.mm"
include "mpan.mm"
include "syl6.mm"
include "3impd.mm"
include "syl5bi.mm"
include "df-3an.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"
include "3exbii.mm"
include "wal.mm"
include "wn.mm"
include "nfcvf2.mm"
include "nfcvd.mm"
include "nfeqd.mm"
include "exdistrf.mm"
include "eximi.mm"
include "excom.mm"
include "3imtr4i.mm"
include "anim2i.mm"
include "3syl.mm"
include "sylbi.mm"
include "syl11.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "3exbidv.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "adantr.mm"
include "exlimivv.mm"
include "com3l.mm"
include "mpdd.mm"
include "mpcom.mm"
include "19.8a.mm"
include "ex.mm"
include "impbid.mm"
include "df-oprab.mm"
include "elab2.mm"

theorem oprabid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w


  assert |- ( <. <. x , y >. , z >. e. { <. <. x , y >. , z >. | ph } <-> ph )

  proof
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
    #
    vy
    wex
    #
    vx
    wex
    #
    wph
    vw
    @5
    wph
    vx
    vy
    vz
    coprab
    @3
    @4
    opex
    @6
    @10
    wph
    @0
    va
    cv
    #
    vt
    cv
    #
    cop
    #
    wceq
    #
    @13
    @5
    wceq
    #
    wa
    #
    vt
    wex
    va
    wex
    #
    @6
    @10
    wph
    wi
    #
    @6
    @17
    va
    vt
    @0
    @3
    @4
    @1
    @2
    opex
    vz
    vex
    #
    eqvinop
    biimpi
    @16
    @6
    @18
    wi
    #
    va
    vt
    @14
    @20
    @15
    @14
    @6
    @11
    @3
    wceq
    #
    @18
    @14
    @6
    @15
    @21
    @0
    @13
    @5
    eqeq1
    @11
    @12
    @3
    @4
    va
    vex
    vt
    vex
    opth1
    syl6bi
    @21
    @14
    @6
    @18
    @21
    @11
    vr
    cv
    #
    vs
    cv
    #
    cop
    #
    wceq
    #
    @24
    @3
    wceq
    #
    wa
    #
    vs
    wex
    vr
    wex
    @14
    @20
    wi
    #
    vr
    vs
    @11
    @1
    @2
    vx
    vex
    #
    vy
    vex
    #
    eqvinop
    @27
    @28
    vr
    vs
    @25
    @28
    @26
    @25
    @14
    @0
    @24
    @12
    cop
    #
    wceq
    #
    @20
    @25
    @13
    @31
    @0
    @11
    @24
    @12
    opeq1
    eqeq2d
    @32
    @20
    @5
    @31
    wceq
    #
    @33
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
    wph
    wi
    #
    wi
    vx
    vr
    weq
    #
    vy
    vs
    weq
    #
    vz
    vt
    weq
    #
    wph
    wa
    #
    vz
    wex
    #
    wa
    vy
    wex
    #
    wa
    #
    vx
    wex
    #
    @33
    wph
    @35
    @33
    @37
    @38
    @39
    w3a
    #
    @44
    wph
    @1
    @2
    @22
    @23
    @4
    @12
    @29
    @30
    @19
    otth2
    #
    @44
    @37
    @38
    @39
    wph
    @44
    @37
    @42
    @38
    @39
    wph
    wi
    #
    wi
    @37
    vx
    weu
    @44
    @37
    @42
    wi
    vx
    vr
    euequ1
    @37
    @42
    vx
    eupick
    mpan
    @42
    @38
    @41
    @47
    @38
    vy
    weu
    @42
    @38
    @41
    wi
    vy
    vs
    euequ1
    @38
    @41
    vy
    eupick
    mpan
    @39
    vz
    weu
    @41
    @47
    vz
    vt
    euequ1
    @39
    wph
    vz
    eupick
    mpan
    syl6
    syl6
    3impd
    syl5bi
    @35
    @37
    @38
    @40
    wa
    #
    wa
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @44
    @34
    @49
    vx
    vy
    vz
    @34
    @37
    @38
    wa
    #
    @39
    wa
    #
    wph
    wa
    @52
    @40
    wa
    @49
    @33
    @53
    wph
    @33
    @45
    @53
    @46
    @37
    @38
    @39
    df-3an
    bitri
    anbi1i
    @52
    @39
    wph
    anass
    @37
    @38
    @40
    anass
    3bitri
    3exbii
    @51
    @37
    @48
    vz
    wex
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @37
    @54
    vy
    wex
    #
    wa
    #
    vx
    wex
    @44
    @50
    vx
    wex
    #
    vy
    wex
    @55
    vx
    wex
    #
    vy
    wex
    @51
    @56
    @59
    @60
    vy
    @37
    @48
    vx
    vz
    vx
    vz
    weq
    vx
    wal
    wn
    #
    vz
    @1
    @22
    vx
    vz
    nfcvf2
    @61
    vz
    @22
    nfcvd
    nfeqd
    exdistrf
    eximi
    @50
    vx
    vy
    excom
    @55
    vx
    vy
    excom
    3imtr4i
    @37
    @54
    vx
    vy
    vx
    vy
    weq
    vx
    wal
    wn
    #
    vy
    @1
    @22
    vx
    vy
    nfcvf2
    @62
    vy
    @22
    nfcvd
    nfeqd
    exdistrf
    @58
    @43
    vx
    @57
    @42
    @37
    @38
    @40
    vy
    vz
    vy
    vz
    weq
    vy
    wal
    wn
    #
    vz
    @2
    @23
    vy
    vz
    nfcvf2
    @63
    vz
    @23
    nfcvd
    nfeqd
    exdistrf
    anim2i
    eximi
    3syl
    sylbi
    syl11
    @32
    @6
    @33
    @18
    @36
    @32
    @6
    @31
    @5
    wceq
    @33
    @0
    @31
    @5
    eqeq1
    @31
    @5
    eqcom
    syl6bb
    #
    @32
    @10
    @35
    wph
    @32
    @7
    @34
    vx
    vy
    vz
    @32
    @6
    @33
    wph
    @64
    anbi1d
    3exbidv
    imbi1d
    imbi12d
    mpbiri
    syl6bi
    adantr
    exlimivv
    sylbi
    com3l
    mpdd
    adantr
    exlimivv
    mpcom
    @6
    wph
    @10
    @7
    @8
    @9
    @10
    @7
    vz
    19.8a
    @8
    vy
    19.8a
    @9
    vx
    19.8a
    3syl
    ex
    impbid
    wph
    vx
    vy
    vz
    vw
    df-oprab
    elab2
end
