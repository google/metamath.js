include "co.mm"
include "wsbc.mm"
include "wcel.mm"
include "wb.mm"
include "cmnd.mm"
include "mndidcl.mm"
include "syl.mm"
include "sbcieg.mm"
include "mpbird.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "csubmnd.mm"
include "cfv.mm"
include "cmrc.mm"
include "cmre.mm"
include "wss.mm"
include "cacs.mm"
include "submacs.mm"
include "acsmred.mm"
include "wa.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "vex.mm"
include "sbcie.mm"
include "dfsbcq.mm"
include "syl5bbr.mm"
include "oveq1.mm"
include "sbceq1d.mm"
include "imbi12d.mm"
include "anbi1d.mm"
include "ovex.mm"
include "oveq2.mm"
include "imbi2d.mm"
include "w3a.mm"
include "ex.mm"
include "3expa.mm"
include "an32s.mm"
include "chvarv.mm"
include "ralrimiva.mm"
include "ssrabdv.mm"
include "wceq.mm"
include "mndrid.mm"
include "sylan.mm"
include "biimprd.mm"
include "simprrl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplrl.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "mndass.mm"
include "syl13anc.mm"
include "sylan9eqr.mm"
include "rspcdv.mm"
include "ralrimdva.mm"
include "impr.mm"
include "cbvralv.mm"
include "sylib.mm"
include "adantrrl.mm"
include "imim1.mm"
include "ral2imi.mm"
include "sylc.mm"
include "ralbidv.mm"
include "issubmd.mm"
include "eqid.mm"
include "mrcsscl.mm"
include "eqsstrd.mm"
include "sseldd.mm"
include "elrab.mm"
include "simprbi.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "mpd.mm"
include "mndlid.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem mrcmndind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cM: class M
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume mrcmndind.ch: |- ( x = y -> ( ps <-> ch ) )
  assume mrcmndind.th: |- ( x = ( y .+ z ) -> ( ps <-> th ) )
  assume mrcmndind.ta: |- ( x = .0. -> ( ps <-> ta ) )
  assume mrcmndind.et: |- ( x = A -> ( ps <-> et ) )
  assume mrcmndind.0g: |- .0. = ( 0g ` M )
  assume mrcmndind.pg: |- .+ = ( +g ` M )
  assume mrcmndind.b: |- B = ( Base ` M )
  assume mrcmndind.m: |- ( ph -> M e. Mnd )
  assume mrcmndind.g: |- ( ph -> G C_ B )
  assume mrcmndind.k: |- ( ph -> B = ( ( mrCls ` ( SubMnd ` M ) ) ` G ) )
  assume mrcmndind.i1: |- ( ph -> ta )
  assume mrcmndind.i2: |- ( ( ( ph /\ y e. B /\ z e. G ) /\ ch ) -> th )
  assume mrcmndind.a: |- ( ph -> A e. B )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ps y
  disjoint ps z
  disjoint ch x
  disjoint ch z
  disjoint th x
  disjoint .0. x
  disjoint A x
  disjoint ta x
  disjoint et x
  disjoint G y
  disjoint G z
  disjoint B y
  disjoint B z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint a ps
  disjoint b ps
  disjoint c ps
  disjoint d ps
  disjoint .0. a
  disjoint .0. b
  disjoint A a
  disjoint A b
  disjoint G a
  disjoint G b
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ d
  disjoint M c
  disjoint M d
  assert |- ( ph -> et )

  proof
    wph
    wps
    vx
    c.0
    cA
    c.pl
    co
    #
    wsbc
    #
    wet
    wph
    wps
    vx
    c.0
    wsbc
    #
    @1
    wph
    @2
    wta
    mrcmndind.i1
    wph
    c.0
    cB
    wcel
    #
    @2
    wta
    wb
    wph
    cM
    cmnd
    wcel
    #
    @3
    mrcmndind.m
    cB
    cM
    c.0
    mrcmndind.b
    mrcmndind.0g
    mndidcl
    syl
    #
    wps
    wta
    vx
    c.0
    cB
    mrcmndind.ta
    sbcieg
    syl
    mpbird
    wph
    @3
    wps
    vx
    va
    cv
    #
    wsbc
    #
    wps
    vx
    @6
    cA
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    va
    cB
    wral
    #
    @2
    @1
    wi
    #
    @5
    wph
    cA
    @7
    wps
    vx
    @6
    vb
    cv
    #
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    va
    cB
    wral
    #
    vb
    cB
    crab
    #
    wcel
    #
    @11
    wph
    cB
    @18
    cA
    wph
    cB
    cG
    cM
    csubmnd
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    @18
    mrcmndind.k
    wph
    @20
    cB
    cmre
    cfv
    wcel
    cG
    @18
    wss
    @18
    @20
    wcel
    @22
    @18
    wss
    wph
    @20
    cB
    wph
    @4
    @20
    cB
    cacs
    cfv
    wcel
    mrcmndind.m
    cB
    cM
    mrcmndind.b
    submacs
    syl
    acsmred
    wph
    @17
    vb
    cB
    cG
    mrcmndind.g
    wph
    @13
    cG
    wcel
    #
    wa
    #
    @16
    va
    cB
    @24
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wch
    wps
    vx
    @25
    @13
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    wi
    #
    @24
    @6
    cB
    wcel
    #
    wa
    #
    @16
    wi
    vy
    va
    vy
    va
    weq
    #
    @27
    @33
    @30
    @16
    @34
    @26
    @32
    @24
    @25
    @6
    cB
    eleq1
    anbi2d
    @34
    wch
    @7
    @29
    @15
    wch
    wps
    vx
    @25
    wsbc
    @34
    @7
    wps
    wch
    vx
    @25
    vy
    vex
    mrcmndind.ch
    sbcie
    wps
    vx
    @25
    @6
    dfsbcq
    syl5bbr
    @34
    wps
    vx
    @28
    @14
    @25
    @6
    @13
    c.pl
    oveq1
    sbceq1d
    imbi12d
    imbi12d
    wph
    vz
    cv
    #
    cG
    wcel
    #
    wa
    #
    @26
    wa
    #
    wch
    wth
    wi
    #
    wi
    @31
    vz
    vb
    vz
    vb
    weq
    #
    @38
    @27
    @39
    @30
    @40
    @37
    @24
    @26
    @40
    @36
    @23
    wph
    @35
    @13
    cG
    eleq1
    anbi2d
    anbi1d
    @40
    wth
    @29
    wch
    wth
    wps
    vx
    @25
    @35
    c.pl
    co
    #
    wsbc
    @40
    @29
    wps
    wth
    vx
    @41
    @25
    @35
    c.pl
    ovex
    mrcmndind.th
    sbcie
    @40
    wps
    vx
    @41
    @28
    @35
    @13
    @25
    c.pl
    oveq2
    sbceq1d
    syl5bbr
    imbi2d
    imbi12d
    wph
    @26
    @36
    @39
    wph
    @26
    @36
    @39
    wph
    @26
    @36
    w3a
    wch
    wth
    mrcmndind.i2
    ex
    3expa
    an32s
    chvarv
    chvarv
    ralrimiva
    ssrabdv
    wph
    @17
    @7
    wps
    vx
    @6
    c.0
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    va
    cB
    wral
    @7
    wps
    vx
    @6
    vc
    cv
    #
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    va
    cB
    wral
    #
    @7
    wps
    vx
    @6
    vd
    cv
    #
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    va
    cB
    wral
    #
    @7
    wps
    vx
    @6
    @45
    @50
    c.pl
    co
    #
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    va
    cB
    wral
    #
    vc
    vd
    vb
    cB
    c.pl
    cM
    c.0
    mrcmndind.b
    mrcmndind.pg
    mrcmndind.0g
    mrcmndind.m
    wph
    @44
    va
    cB
    wph
    @32
    wa
    #
    @43
    @7
    @60
    wps
    vx
    @42
    @6
    wph
    @4
    @32
    @42
    @6
    wceq
    mrcmndind.m
    cB
    c.pl
    cM
    @6
    c.0
    mrcmndind.b
    mrcmndind.pg
    mrcmndind.0g
    mndrid
    sylan
    sbceq1d
    biimprd
    ralrimiva
    wph
    @45
    cB
    wcel
    #
    @50
    cB
    wcel
    #
    wa
    #
    @49
    @54
    wa
    wa
    wa
    @49
    @47
    @57
    wi
    #
    va
    cB
    wral
    #
    @59
    wph
    @63
    @49
    @54
    simprrl
    wph
    @63
    @54
    @65
    @49
    wph
    @63
    @54
    wa
    wa
    wps
    vx
    @13
    @45
    c.pl
    co
    #
    wsbc
    #
    wps
    vx
    @13
    @55
    c.pl
    co
    #
    wsbc
    #
    wi
    #
    vb
    cB
    wral
    #
    @65
    wph
    @63
    @54
    @71
    wph
    @63
    wa
    #
    @54
    @70
    vb
    cB
    @72
    @13
    cB
    wcel
    #
    wa
    #
    @53
    @70
    va
    @66
    cB
    @74
    @4
    @73
    @61
    @66
    cB
    wcel
    wph
    @4
    @63
    @73
    mrcmndind.m
    ad2antrr
    #
    @72
    @73
    simpr
    #
    wph
    @61
    @62
    @73
    simplrl
    #
    cB
    c.pl
    cM
    @13
    @45
    mrcmndind.b
    mrcmndind.pg
    mndcl
    syl3anc
    @74
    @6
    @66
    wceq
    #
    wa
    #
    @7
    @67
    @52
    @69
    @79
    wps
    vx
    @6
    @66
    @74
    @78
    simpr
    sbceq1d
    @79
    wps
    vx
    @51
    @68
    @78
    @74
    @51
    @66
    @50
    c.pl
    co
    #
    @68
    @6
    @66
    @50
    c.pl
    oveq1
    @74
    @4
    @73
    @61
    @62
    @80
    @68
    wceq
    @75
    @76
    @77
    wph
    @61
    @62
    @73
    simplrr
    cB
    c.pl
    cM
    @13
    @45
    @50
    mrcmndind.b
    mrcmndind.pg
    mndass
    syl13anc
    sylan9eqr
    sbceq1d
    imbi12d
    rspcdv
    ralrimdva
    impr
    @70
    @64
    vb
    va
    cB
    vb
    va
    weq
    #
    @67
    @47
    @69
    @57
    @81
    wps
    vx
    @66
    @46
    @13
    @6
    @45
    c.pl
    oveq1
    sbceq1d
    @81
    wps
    vx
    @68
    @56
    @13
    @6
    @55
    c.pl
    oveq1
    sbceq1d
    imbi12d
    cbvralv
    sylib
    adantrrl
    @48
    @64
    @58
    va
    cB
    @7
    @47
    @57
    imim1
    ral2imi
    sylc
    @13
    c.0
    wceq
    #
    @16
    @44
    va
    cB
    @82
    @15
    @43
    @7
    @82
    wps
    vx
    @14
    @42
    @13
    c.0
    @6
    c.pl
    oveq2
    sbceq1d
    imbi2d
    ralbidv
    vb
    vc
    weq
    #
    @16
    @48
    va
    cB
    @83
    @15
    @47
    @7
    @83
    wps
    vx
    @14
    @46
    @13
    @45
    @6
    c.pl
    oveq2
    sbceq1d
    imbi2d
    ralbidv
    vb
    vd
    weq
    #
    @16
    @53
    va
    cB
    @84
    @15
    @52
    @7
    @84
    wps
    vx
    @14
    @51
    @13
    @50
    @6
    c.pl
    oveq2
    sbceq1d
    imbi2d
    ralbidv
    @13
    @55
    wceq
    #
    @16
    @58
    va
    cB
    @85
    @15
    @57
    @7
    @85
    wps
    vx
    @14
    @56
    @13
    @55
    @6
    c.pl
    oveq2
    sbceq1d
    imbi2d
    ralbidv
    issubmd
    @20
    cG
    @21
    @18
    cB
    @21
    eqid
    mrcsscl
    syl3anc
    eqsstrd
    mrcmndind.a
    sseldd
    @19
    cA
    cB
    wcel
    #
    @11
    @17
    @11
    vb
    cA
    cB
    @13
    cA
    wceq
    #
    @16
    @10
    va
    cB
    @87
    @15
    @9
    @7
    @87
    wps
    vx
    @14
    @8
    @13
    cA
    @6
    c.pl
    oveq2
    sbceq1d
    imbi2d
    ralbidv
    elrab
    simprbi
    syl
    @10
    @12
    va
    c.0
    cB
    @6
    c.0
    wceq
    #
    @7
    @2
    @9
    @1
    wps
    vx
    @6
    c.0
    dfsbcq
    @88
    wps
    vx
    @8
    @0
    @6
    c.0
    cA
    c.pl
    oveq1
    sbceq1d
    imbi12d
    rspcva
    syl2anc
    mpd
    wph
    @1
    wps
    vx
    cA
    wsbc
    #
    wet
    wph
    wps
    vx
    @0
    cA
    wph
    @4
    @86
    @0
    cA
    wceq
    mrcmndind.m
    mrcmndind.a
    cB
    c.pl
    cM
    cA
    c.0
    mrcmndind.b
    mrcmndind.pg
    mrcmndind.0g
    mndlid
    syl2anc
    sbceq1d
    wph
    @86
    @89
    wet
    wb
    mrcmndind.a
    wps
    wet
    vx
    cA
    cB
    mrcmndind.et
    sbcieg
    syl
    bitrd
    mpbid
end
