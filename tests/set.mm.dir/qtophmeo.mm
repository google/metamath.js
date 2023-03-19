include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "cqtop.mm"
include "co.mm"
include "chmeo.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "ccn.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wfn.mm"
include "wfo.mm"
include "fofn.mm"
include "syl.mm"
include "qtopid.mm"
include "syl2anc.mm"
include "w3a.mm"
include "df-3an.mm"
include "biimpd.mm"
include "impr.mm"
include "sylan2b.mm"
include "qtopeu.mm"
include "reurex.mm"
include "ccnv.mm"
include "simprl.mm"
include "biimprd.mm"
include "adantr.mm"
include "wf.mm"
include "qtoptopon.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "cid.mm"
include "cres.mm"
include "coeq1.mm"
include "eqeq2d.mm"
include "simpr3.mm"
include "cnco.mm"
include "idcn.mm"
include "simprr.mm"
include "simplrr.mm"
include "coeq2d.mm"
include "eqtrd.mm"
include "coass.mm"
include "syl6eqr.mm"
include "fof.mm"
include "fcoi2.mm"
include "eqcomd.mm"
include "reu2eqd.mm"
include "2fcoidinvd.mm"
include "eqeltrd.mm"
include "rexlimddv.mm"
include "ishmeo.mm"
include "sylanbrc.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "eqtr2.mm"
include "wb.mm"
include "wf1o.mm"
include "hmeof1o2.mm"
include "f1ofn.mm"
include "cocan2.mm"
include "syl5ib.mm"
include "ralrimivva.mm"
include "reu4.mm"

theorem qtophmeo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vh: setvar h
  assume qtophmeo.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume qtophmeo.3: |- ( ph -> F : X -onto-> Y )
  assume qtophmeo.4: |- ( ph -> G : X -onto-> Y )
  assume qtophmeo.5: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( ( F ` x ) = ( F ` y ) <-> ( G ` x ) = ( G ` y ) ) )

  disjoint f x
  disjoint f y
  disjoint F f
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint J f
  disjoint J x
  disjoint J y
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y x
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint G g
  disjoint G h
  disjoint J g
  disjoint J h
  disjoint g ph
  disjoint h ph
  disjoint Y g
  disjoint Y h
  assert |- ( ph -> E! f e. ( ( J qTop F ) Homeo ( J qTop G ) ) G = ( f o. F ) )

  proof
    wph
    cG
    vf
    cv
    #
    cF
    ccom
    #
    wceq
    #
    vf
    cJ
    cF
    cqtop
    co
    #
    cJ
    cG
    cqtop
    co
    #
    chmeo
    co
    #
    wrex
    #
    @2
    cG
    vg
    cv
    #
    cF
    ccom
    #
    wceq
    #
    wa
    #
    vf
    vg
    weq
    #
    wi
    #
    vg
    @5
    wral
    vf
    @5
    wral
    @2
    vf
    @5
    wreu
    wph
    @2
    vf
    @3
    @4
    ccn
    co
    #
    wrex
    #
    @6
    wph
    @2
    vf
    @13
    wreu
    @14
    wph
    vx
    vy
    vf
    cF
    cG
    cJ
    @4
    cX
    cY
    qtophmeo.2
    qtophmeo.3
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cG
    cX
    wfn
    #
    cG
    cJ
    @4
    ccn
    co
    wcel
    qtophmeo.2
    wph
    cX
    cY
    cG
    wfo
    #
    @16
    qtophmeo.4
    cX
    cY
    cG
    fofn
    syl
    cG
    cJ
    cX
    qtopid
    syl2anc
    #
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    @19
    cF
    cfv
    @21
    cF
    cfv
    wceq
    #
    w3a
    wph
    @20
    @22
    wa
    #
    @23
    wa
    @19
    cG
    cfv
    @21
    cG
    cfv
    wceq
    #
    @20
    @22
    @23
    df-3an
    wph
    @24
    @23
    @25
    wph
    @24
    wa
    #
    @23
    @25
    qtophmeo.5
    biimpd
    impr
    sylan2b
    qtopeu
    @2
    vf
    @13
    reurex
    syl
    wph
    @2
    @2
    vf
    @13
    @5
    wph
    @0
    @13
    wcel
    #
    @2
    wa
    #
    @0
    @5
    wcel
    #
    @2
    wa
    wph
    @28
    wa
    #
    @29
    @2
    @30
    @27
    @0
    ccnv
    #
    @4
    @3
    ccn
    co
    #
    wcel
    #
    @29
    wph
    @27
    @2
    simprl
    @30
    cF
    @7
    cG
    ccom
    #
    wceq
    #
    @33
    vg
    @32
    @30
    @35
    vg
    @32
    wreu
    #
    @35
    vg
    @32
    wrex
    wph
    @36
    @28
    wph
    vx
    vy
    vg
    cG
    cF
    cJ
    @3
    cX
    cY
    qtophmeo.2
    qtophmeo.4
    wph
    @15
    cF
    cX
    wfn
    #
    cF
    cJ
    @3
    ccn
    co
    wcel
    qtophmeo.2
    wph
    cX
    cY
    cF
    wfo
    #
    @37
    qtophmeo.3
    cX
    cY
    cF
    fofn
    syl
    cF
    cJ
    cX
    qtopid
    syl2anc
    #
    @20
    @22
    @25
    w3a
    wph
    @24
    @25
    wa
    @23
    @20
    @22
    @25
    df-3an
    wph
    @24
    @25
    @23
    @26
    @23
    @25
    qtophmeo.5
    biimprd
    impr
    sylan2b
    qtopeu
    adantr
    @35
    vg
    @32
    reurex
    syl
    @30
    @7
    @32
    wcel
    #
    @35
    wa
    #
    wa
    #
    @31
    @7
    @32
    @42
    cY
    cY
    @0
    @7
    @42
    @3
    cY
    ctopon
    cfv
    #
    wcel
    #
    @4
    @43
    wcel
    #
    @27
    cY
    cY
    @0
    wf
    wph
    @44
    @28
    @41
    wph
    @15
    @38
    @44
    qtophmeo.2
    qtophmeo.3
    cF
    cJ
    cX
    cY
    qtoptopon
    syl2anc
    #
    ad2antrr
    #
    wph
    @45
    @28
    @41
    wph
    @15
    @17
    @45
    qtophmeo.2
    qtophmeo.4
    cG
    cJ
    cX
    cY
    qtoptopon
    syl2anc
    #
    ad2antrr
    #
    wph
    @27
    @2
    @41
    simplrl
    #
    @0
    @3
    @4
    cY
    cY
    cnf2
    syl3anc
    @42
    @45
    @44
    @40
    cY
    cY
    @7
    wf
    @49
    @47
    @30
    @40
    @35
    simprl
    #
    @7
    @4
    @3
    cY
    cY
    cnf2
    syl3anc
    @42
    cF
    vh
    cv
    #
    cF
    ccom
    #
    wceq
    #
    cF
    @7
    @0
    ccom
    #
    cF
    ccom
    #
    wceq
    cF
    cid
    cY
    cres
    #
    cF
    ccom
    #
    wceq
    vh
    @3
    @3
    ccn
    co
    #
    @55
    @57
    @52
    @55
    wceq
    @53
    @56
    cF
    @52
    @55
    cF
    coeq1
    eqeq2d
    @52
    @57
    wceq
    #
    @53
    @58
    cF
    @52
    @57
    cF
    coeq1
    eqeq2d
    wph
    @54
    vh
    @59
    wreu
    @28
    @41
    wph
    vx
    vy
    vh
    cF
    cF
    cJ
    @3
    cX
    cY
    qtophmeo.2
    qtophmeo.3
    @39
    wph
    @20
    @22
    @23
    simpr3
    qtopeu
    ad2antrr
    @42
    @27
    @40
    @55
    @59
    wcel
    @50
    @51
    @0
    @7
    @3
    @4
    @3
    cnco
    syl2anc
    wph
    @57
    @59
    wcel
    #
    @28
    @41
    wph
    @44
    @61
    @46
    @3
    cY
    idcn
    syl
    ad2antrr
    @42
    cF
    @7
    @1
    ccom
    #
    @56
    @42
    cF
    @34
    @62
    @30
    @40
    @35
    simprr
    #
    @42
    cG
    @1
    @7
    wph
    @27
    @2
    @41
    simplrr
    #
    coeq2d
    eqtrd
    @7
    @0
    cF
    coass
    syl6eqr
    @42
    @58
    cF
    @42
    cX
    cY
    cF
    wf
    #
    @58
    cF
    wceq
    wph
    @65
    @28
    @41
    wph
    @38
    @65
    qtophmeo.3
    cX
    cY
    cF
    fof
    syl
    ad2antrr
    cX
    cY
    cF
    fcoi2
    syl
    eqcomd
    reu2eqd
    @42
    cG
    @52
    cG
    ccom
    #
    wceq
    #
    cG
    @0
    @7
    ccom
    #
    cG
    ccom
    #
    wceq
    cG
    @57
    cG
    ccom
    #
    wceq
    vh
    @4
    @4
    ccn
    co
    #
    @68
    @57
    @52
    @68
    wceq
    @66
    @69
    cG
    @52
    @68
    cG
    coeq1
    eqeq2d
    @60
    @66
    @70
    cG
    @52
    @57
    cG
    coeq1
    eqeq2d
    wph
    @67
    vh
    @71
    wreu
    @28
    @41
    wph
    vx
    vy
    vh
    cG
    cG
    cJ
    @4
    cX
    cY
    qtophmeo.2
    qtophmeo.4
    @18
    wph
    @20
    @22
    @25
    simpr3
    qtopeu
    ad2antrr
    @42
    @40
    @27
    @68
    @71
    wcel
    @51
    @50
    @7
    @0
    @4
    @3
    @4
    cnco
    syl2anc
    wph
    @57
    @71
    wcel
    #
    @28
    @41
    wph
    @45
    @72
    @48
    @4
    cY
    idcn
    syl
    ad2antrr
    @42
    cG
    @0
    @34
    ccom
    #
    @69
    @42
    cG
    @1
    @73
    @64
    @42
    cF
    @34
    @0
    @63
    coeq2d
    eqtrd
    @0
    @7
    cG
    coass
    syl6eqr
    @42
    @70
    cG
    @42
    cX
    cY
    cG
    wf
    #
    @70
    cG
    wceq
    wph
    @74
    @28
    @41
    wph
    @17
    @74
    qtophmeo.4
    cX
    cY
    cG
    fof
    syl
    ad2antrr
    cX
    cY
    cG
    fcoi2
    syl
    eqcomd
    reu2eqd
    2fcoidinvd
    @51
    eqeltrd
    rexlimddv
    @0
    @3
    @4
    ishmeo
    sylanbrc
    wph
    @27
    @2
    simprr
    jca
    ex
    reximdv2
    mpd
    wph
    @12
    vf
    vg
    @5
    @5
    @10
    @1
    @8
    wceq
    #
    wph
    @29
    @7
    @5
    wcel
    #
    wa
    #
    wa
    #
    @11
    cG
    @1
    @8
    eqtr2
    @78
    @38
    @0
    cY
    wfn
    #
    @7
    cY
    wfn
    #
    @75
    @11
    wb
    wph
    @38
    @77
    qtophmeo.3
    adantr
    @78
    cY
    cY
    @0
    wf1o
    #
    @79
    @78
    @44
    @45
    @29
    @81
    wph
    @44
    @77
    @46
    adantr
    #
    wph
    @45
    @77
    @48
    adantr
    #
    wph
    @29
    @76
    simprl
    @0
    @3
    @4
    cY
    cY
    hmeof1o2
    syl3anc
    cY
    cY
    @0
    f1ofn
    syl
    @78
    cY
    cY
    @7
    wf1o
    #
    @80
    @78
    @44
    @45
    @76
    @84
    @82
    @83
    wph
    @29
    @76
    simprr
    @7
    @3
    @4
    cY
    cY
    hmeof1o2
    syl3anc
    cY
    cY
    @7
    f1ofn
    syl
    cX
    cY
    cF
    @0
    @7
    cocan2
    syl3anc
    syl5ib
    ralrimivva
    @2
    @9
    vf
    vg
    @5
    @11
    @1
    @8
    cG
    @0
    @7
    cF
    coeq1
    eqeq2d
    reu4
    sylanbrc
end
