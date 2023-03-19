include "cvv.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "crab.mm"
include "wcel.mm"
include "pwexg.mm"
include "syl.mm"
include "rabexg.mm"
include "syl5eqel.mm"
include "c0.mm"
include "wa.mm"
include "0elpw.mm"
include "a1i.mm"
include "cfn.mm"
include "0fin.mm"
include "fict.mm"
include "ax-mp.mm"
include "orci.mm"
include "jca.mm"
include "wceq.mm"
include "breq1.mm"
include "difeq2.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "elrab2.mm"
include "sylibr.mm"
include "cuni.mm"
include "wss.mm"
include "wral.mm"
include "csn.mm"
include "snidg.mm"
include "snelpwi.mm"
include "snfi.mm"
include "elunii.mm"
include "syl2anc.mm"
include "rgen.mm"
include "dfss3.mm"
include "mpbir.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"
include "eqssi.mm"
include "difssd.mm"
include "wb.mm"
include "ssexd.mm"
include "elpwg.mm"
include "mpbird.mm"
include "ad2antrr.mm"
include "sseli.mm"
include "elpwi.mm"
include "dfss4.mm"
include "sylib.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "olc.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "wn.mm"
include "rabeq2i.mm"
include "biimpi.mm"
include "simprd.mm"
include "adantl.mm"
include "adantr.mm"
include "pm2.53.mm"
include "sylc.mm"
include "orc.mm"
include "pm2.61dan.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "unissb.mm"
include "vuniex.mm"
include "elpw.mm"
include "id.mm"
include "adantll.mm"
include "unictb.mm"
include "3syl.mm"
include "wrex.mm"
include "rexnal.mm"
include "bicomi.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfn.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "elssuni.mm"
include "3ad2ant2.mm"
include "sscond.mm"
include "3adant3.mm"
include "simp3.mm"
include "ssct.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "adantlr.mm"
include "3adant1.mm"
include "issald.mm"

theorem salexct
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cV: class V
  let vy: setvar y
  let vk: setvar k
  assume salexct.a: |- ( ph -> A e. V )
  assume salexct.b: |- S = { x e. ~P A | ( x ~<_ _om \/ ( A \ x ) ~<_ _om ) }

  disjoint A x
  disjoint S x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint S y
  disjoint k x
  assert |- ( ph -> S e. SAlg )

  proof
    wph
    vx
    cS
    cvv
    cA
    wph
    cS
    vx
    cv
    #
    com
    cdom
    wbr
    #
    cA
    @0
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    vx
    cA
    cpw
    #
    crab
    #
    cvv
    salexct.b
    wph
    @5
    cvv
    wcel
    #
    @6
    cvv
    wcel
    wph
    cA
    cV
    wcel
    @7
    salexct.a
    cA
    cV
    pwexg
    syl
    @4
    vx
    @5
    cvv
    rabexg
    syl
    syl5eqel
    wph
    c0
    @5
    wcel
    #
    c0
    com
    cdom
    wbr
    #
    cA
    c0
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    c0
    cS
    wcel
    wph
    @8
    @12
    @8
    wph
    cA
    0elpw
    a1i
    @12
    wph
    @9
    @11
    c0
    cfn
    wcel
    @9
    0fin
    c0
    fict
    ax-mp
    orci
    a1i
    jca
    @4
    @12
    vx
    c0
    @5
    cS
    @0
    c0
    wceq
    #
    @1
    @9
    @3
    @11
    @0
    c0
    com
    cdom
    breq1
    @13
    @2
    @10
    com
    cdom
    @0
    c0
    cA
    difeq2
    breq1d
    orbi12d
    salexct.b
    elrab2
    sylibr
    cA
    cS
    cuni
    #
    cA
    @14
    wss
    vy
    cv
    #
    @14
    wcel
    #
    vy
    cA
    wral
    @16
    vy
    cA
    @15
    cA
    wcel
    #
    @15
    @15
    csn
    #
    wcel
    @18
    cS
    wcel
    #
    @16
    @15
    cA
    snidg
    @17
    @18
    @5
    wcel
    #
    @18
    com
    cdom
    wbr
    #
    cA
    @18
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    @19
    @17
    @20
    @24
    @15
    cA
    snelpwi
    @24
    @17
    @21
    @23
    @18
    cfn
    wcel
    @21
    @15
    snfi
    @18
    fict
    ax-mp
    orci
    a1i
    jca
    @4
    @24
    vx
    @18
    @5
    cS
    @0
    @18
    wceq
    #
    @1
    @21
    @3
    @23
    @0
    @18
    com
    cdom
    breq1
    @25
    @2
    @22
    com
    cdom
    @0
    @18
    cA
    difeq2
    breq1d
    orbi12d
    salexct.b
    elrab2
    sylibr
    @15
    @18
    cS
    elunii
    syl2anc
    rgen
    vy
    cA
    @14
    dfss3
    mpbir
    @14
    @5
    cuni
    cA
    cS
    @5
    cS
    @6
    @5
    salexct.b
    @4
    vx
    @5
    ssrab2
    eqsstri
    #
    unissi
    cA
    unipw
    sseqtri
    eqssi
    wph
    @0
    cS
    wcel
    #
    wa
    #
    @1
    @2
    cS
    wcel
    #
    @28
    @1
    wa
    #
    @2
    @5
    wcel
    #
    @3
    cA
    @2
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    #
    @29
    @30
    @31
    @34
    wph
    @31
    @27
    @1
    wph
    @31
    @2
    cA
    wss
    #
    wph
    cA
    @0
    difssd
    #
    wph
    @2
    cvv
    wcel
    @31
    @36
    wb
    wph
    @2
    cA
    cV
    salexct.a
    @37
    ssexd
    @2
    cA
    cvv
    elpwg
    syl
    mpbird
    #
    ad2antrr
    @30
    @33
    @34
    @30
    @32
    @0
    com
    cdom
    @27
    @32
    @0
    wceq
    #
    wph
    @1
    @27
    @0
    cA
    wss
    #
    @39
    @27
    @0
    @5
    wcel
    #
    @40
    cS
    @5
    @0
    @26
    sseli
    @0
    cA
    elpwi
    syl
    @0
    cA
    dfss4
    sylib
    ad2antlr
    @28
    @1
    simpr
    eqbrtrd
    @33
    @3
    olc
    syl
    jca
    @15
    com
    cdom
    wbr
    #
    cA
    @15
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    @34
    vy
    @2
    @5
    cS
    @15
    @2
    wceq
    #
    @42
    @3
    @44
    @33
    @15
    @2
    com
    cdom
    breq1
    @46
    @43
    @32
    com
    cdom
    @15
    @2
    cA
    difeq2
    breq1d
    orbi12d
    cS
    @6
    @45
    vy
    @5
    crab
    salexct.b
    @4
    @45
    vx
    vy
    @5
    @0
    @15
    wceq
    #
    @1
    @42
    @3
    @44
    @0
    @15
    com
    cdom
    breq1
    @47
    @2
    @43
    com
    cdom
    @0
    @15
    cA
    difeq2
    breq1d
    orbi12d
    cbvrabv
    eqtri
    #
    elrab2
    #
    sylibr
    @28
    @1
    wn
    #
    wa
    #
    @35
    @29
    @51
    @31
    @34
    wph
    @31
    @27
    @50
    @38
    ad2antrr
    @51
    @3
    @34
    @51
    @4
    @50
    @3
    @28
    @4
    @50
    @27
    @4
    wph
    @27
    @41
    @4
    @27
    @41
    @4
    wa
    @4
    vx
    cS
    @5
    salexct.b
    rabeq2i
    biimpi
    simprd
    adantl
    adantr
    @28
    @50
    simpr
    @1
    @3
    pm2.53
    sylc
    @3
    @33
    orc
    syl
    jca
    @49
    sylibr
    pm2.61dan
    @0
    cS
    cpw
    wcel
    #
    @1
    @0
    cuni
    #
    cS
    wcel
    #
    wph
    @52
    @1
    wa
    #
    @53
    @5
    wcel
    #
    @53
    com
    cdom
    wbr
    #
    cA
    @53
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    @54
    @55
    @56
    @60
    @52
    @56
    @1
    @52
    @53
    cA
    wss
    #
    @56
    @52
    @15
    cA
    wss
    #
    vy
    @0
    wral
    @61
    @52
    @62
    vy
    @0
    @52
    @15
    @0
    wcel
    #
    wa
    #
    @15
    cS
    wcel
    #
    @62
    @64
    @0
    cS
    @15
    @52
    @0
    cS
    wss
    @63
    @0
    cS
    elpwi
    adantr
    @52
    @63
    simpr
    sseldd
    #
    @65
    @15
    @5
    wcel
    #
    @62
    cS
    @5
    @15
    @26
    sseli
    @15
    cA
    elpwi
    syl
    syl
    ralrimiva
    vy
    @0
    cA
    unissb
    sylibr
    @53
    cA
    vx
    vuniex
    elpw
    sylibr
    adantr
    @55
    @42
    vy
    @0
    wral
    #
    @60
    @55
    @68
    wa
    @1
    @68
    wa
    #
    @57
    @60
    @1
    @68
    @69
    @52
    @69
    id
    adantll
    vy
    @0
    unictb
    @57
    @59
    orc
    3syl
    @52
    @68
    wn
    #
    @60
    @1
    @52
    @70
    wa
    #
    @59
    @60
    @71
    @42
    wn
    #
    vy
    @0
    wrex
    #
    @59
    @70
    @73
    @52
    @70
    @73
    @73
    @70
    @42
    vy
    @0
    rexnal
    bicomi
    biimpi
    adantl
    @71
    @72
    @59
    vy
    @0
    @52
    @70
    vy
    @52
    vy
    nfv
    @68
    vy
    @42
    vy
    @0
    nfra1
    nfn
    nfan
    @59
    vy
    nfv
    @52
    @63
    @72
    @59
    wi
    wi
    @70
    @52
    @63
    @72
    @59
    @52
    @63
    @72
    w3a
    #
    @58
    @43
    wss
    @44
    @59
    @74
    @15
    @53
    cA
    @63
    @52
    @15
    @53
    wss
    @72
    @15
    @0
    elssuni
    3ad2ant2
    sscond
    @74
    @65
    @72
    @44
    @52
    @63
    @65
    @72
    @66
    3adant3
    @52
    @63
    @72
    simp3
    @65
    @72
    wa
    @45
    @72
    @44
    @65
    @45
    @72
    @65
    @67
    @45
    @65
    @67
    @45
    wa
    @45
    vy
    cS
    @5
    @48
    rabeq2i
    biimpi
    simprd
    adantr
    @65
    @72
    simpr
    @42
    @44
    pm2.53
    sylc
    syl2anc
    @58
    @43
    ssct
    syl2anc
    3exp
    adantr
    rexlimd
    mpd
    @59
    @57
    olc
    syl
    adantlr
    pm2.61dan
    jca
    @45
    @60
    vy
    @53
    @5
    cS
    @15
    @53
    wceq
    #
    @42
    @57
    @44
    @59
    @15
    @53
    com
    cdom
    breq1
    @75
    @43
    @58
    com
    cdom
    @15
    @53
    cA
    difeq2
    breq1d
    orbi12d
    @48
    elrab2
    sylibr
    3adant1
    issald
end
