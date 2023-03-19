include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "cfg.mm"
include "co.mm"
include "cfil.mm"
include "wcel.mm"
include "wss.mm"
include "cfm.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cfbas.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "fbsspw.mm"
include "syl.mm"
include "cdm.mm"
include "wf.mm"
include "elfvdm.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "foima.mm"
include "3syl.mm"
include "filtop.mm"
include "fgcl.mm"
include "eqid.mm"
include "imaelfm.mm"
include "syl31anc.mm"
include "eqeltrrd.mm"
include "sseldd.mm"
include "rnelfmlem.mm"
include "unssd.mm"
include "ssun1.mm"
include "fbasne0.mm"
include "ssn0.mm"
include "sylancr.mm"
include "cin.mm"
include "wral.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "0nelfil.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "w3a.mm"
include "3jca.mm"
include "ssfg.mm"
include "sselda.mm"
include "syl2anc.mm"
include "jca.mm"
include "filin.mm"
include "3expa.mm"
include "sylan.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "wex.mm"
include "neq0.mm"
include "elin.mm"
include "wi.mm"
include "wfun.mm"
include "ffun.mm"
include "fvelima.mm"
include "ex.mm"
include "ad3antrrr.mm"
include "fbelss.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "fvimacnv.mm"
include "inelcm.mm"
include "adantl.mm"
include "sylbid.mm"
include "imbi1d.mm"
include "rexlimdva.mm"
include "syld.mm"
include "impd.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "mpd.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "ralrimivv.mm"
include "fbunfip.mm"
include "mpbird.mm"
include "fsubbas.mm"
include "mpbir3and.mm"
include "unexg.mm"
include "ssfii.mm"
include "unssad.mm"
include "sstrd.mm"
include "fmfnfmlem4.mm"
include "elfm.mm"
include "syl3anc.mm"
include "bitr4d.mm"
include "eqrdv.mm"
include "fmfg.mm"
include "eqtrd.mm"
include "sseq2.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem fmfnfm
  let wph: wff ph
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fmfnfm.b: |- ( ph -> B e. ( fBas ` Y ) )
  assume fmfnfm.l: |- ( ph -> L e. ( Fil ` X ) )
  assume fmfnfm.f: |- ( ph -> F : Y --> X )
  assume fmfnfm.fm: |- ( ph -> ( ( X FilMap F ) ` B ) C_ L )

  disjoint B f
  disjoint F f
  disjoint L f
  disjoint X f
  disjoint Y f
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint L s
  disjoint L t
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint ph s
  disjoint ph t
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y s
  disjoint Y t
  disjoint Y w
  disjoint Y x
  disjoint Y z
  assert |- ( ph -> E. f e. ( Fil ` Y ) ( B C_ f /\ L = ( ( X FilMap F ) ` f ) ) )

  proof
    wph
    cY
    cB
    vx
    cL
    cF
    ccnv
    vx
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cun
    #
    cfi
    cfv
    #
    cfg
    co
    #
    cY
    cfil
    cfv
    #
    wcel
    #
    cB
    @6
    wss
    #
    cL
    @6
    cX
    cF
    cfm
    co
    #
    cfv
    #
    wceq
    #
    cB
    vf
    cv
    #
    wss
    #
    cL
    @13
    @10
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @7
    wrex
    wph
    @5
    cY
    cfbas
    cfv
    #
    wcel
    #
    @8
    wph
    @19
    @4
    cY
    cpw
    #
    wss
    #
    @4
    c0
    wne
    #
    c0
    @5
    wcel
    wn
    #
    wph
    cB
    @3
    @20
    wph
    cB
    @18
    wcel
    #
    cB
    @20
    wss
    fmfnfm.b
    cY
    cB
    fbsspw
    syl
    wph
    @3
    @18
    wcel
    #
    @3
    @20
    wss
    wph
    cY
    cfbas
    cdm
    #
    wcel
    #
    cL
    cX
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    cF
    crn
    #
    cL
    wcel
    @25
    wph
    @24
    @27
    fmfnfm.b
    cB
    cY
    cfbas
    elfvdm
    #
    syl
    fmfnfm.l
    fmfnfm.f
    wph
    cB
    @10
    cfv
    #
    cL
    @30
    fmfnfm.fm
    wph
    cF
    cY
    cima
    #
    @30
    @32
    wph
    @29
    cY
    @30
    cF
    wfo
    #
    @33
    @30
    wceq
    fmfnfm.f
    @29
    cF
    cY
    wfn
    @34
    cY
    cX
    cF
    ffn
    cY
    cF
    dffn4
    sylib
    cY
    @30
    cF
    foima
    3syl
    wph
    cX
    cL
    wcel
    #
    @24
    @29
    cY
    cY
    cB
    cfg
    co
    #
    wcel
    #
    @33
    @32
    wcel
    wph
    @28
    @35
    fmfnfm.l
    cL
    cX
    filtop
    syl
    #
    fmfnfm.b
    fmfnfm.f
    wph
    @24
    @36
    @7
    wcel
    @37
    fmfnfm.b
    cB
    cY
    fgcl
    @36
    cY
    filtop
    3syl
    cL
    cB
    cY
    cF
    @36
    cX
    cY
    @36
    eqid
    #
    imaelfm
    syl31anc
    eqeltrrd
    sseldd
    vx
    @26
    cF
    cL
    cX
    cY
    rnelfmlem
    syl31anc
    #
    cY
    @3
    fbsspw
    syl
    unssd
    wph
    cB
    @4
    wss
    cB
    c0
    wne
    #
    @22
    cB
    @3
    ssun1
    wph
    @24
    @41
    fmfnfm.b
    cY
    cB
    fbasne0
    syl
    cB
    @4
    ssn0
    sylancr
    wph
    @23
    vs
    cv
    #
    vt
    cv
    #
    cin
    #
    c0
    wne
    #
    vt
    @3
    wral
    vs
    cB
    wral
    #
    wph
    @45
    vs
    vt
    cB
    @3
    wph
    @42
    cB
    wcel
    #
    @43
    @3
    wcel
    #
    @45
    @48
    @43
    @1
    wceq
    #
    vx
    cL
    wrex
    #
    wph
    @47
    wa
    #
    @45
    @43
    cvv
    wcel
    @48
    @50
    wb
    vt
    vex
    vx
    cL
    @1
    @43
    @2
    cvv
    @2
    eqid
    elrnmpt
    ax-mp
    @51
    @49
    @45
    vx
    cL
    @51
    @0
    cL
    wcel
    #
    wa
    #
    @45
    @49
    @42
    @1
    cin
    #
    c0
    wne
    #
    @53
    cF
    @42
    cima
    #
    @0
    cin
    #
    c0
    wceq
    #
    wn
    #
    @55
    @53
    @58
    c0
    cL
    wcel
    #
    wph
    @60
    wn
    #
    @47
    @52
    wph
    @28
    @61
    fmfnfm.l
    cL
    cX
    0nelfil
    syl
    ad2antrr
    @53
    @57
    cL
    wcel
    #
    @58
    @60
    @51
    @28
    @56
    cL
    wcel
    #
    wa
    @52
    @62
    @51
    @28
    @63
    wph
    @28
    @47
    fmfnfm.l
    adantr
    @51
    @32
    cL
    @56
    wph
    @32
    cL
    wss
    @47
    fmfnfm.fm
    adantr
    @51
    @35
    @24
    @29
    w3a
    #
    @42
    @36
    wcel
    @56
    @32
    wcel
    wph
    @64
    @47
    wph
    @35
    @24
    @29
    @38
    fmfnfm.b
    fmfnfm.f
    3jca
    adantr
    wph
    cB
    @36
    @42
    wph
    @24
    cB
    @36
    wss
    fmfnfm.b
    cB
    cY
    ssfg
    syl
    sselda
    cL
    cB
    @42
    cF
    @36
    cX
    cY
    @39
    imaelfm
    syl2anc
    sseldd
    jca
    @28
    @63
    @52
    @62
    @56
    @0
    cL
    cX
    filin
    3expa
    sylan
    @57
    c0
    cL
    eleq1
    syl5ibcom
    mtod
    @59
    @43
    @57
    wcel
    #
    vt
    wex
    @53
    @55
    vt
    @57
    neq0
    @53
    @65
    @55
    vt
    @65
    @43
    @56
    wcel
    #
    @43
    @0
    wcel
    #
    wa
    @53
    @55
    @43
    @56
    @0
    elin
    @53
    @66
    @67
    @55
    @53
    @66
    vy
    cv
    #
    cF
    cfv
    #
    @43
    wceq
    #
    vy
    @42
    wrex
    #
    @67
    @55
    wi
    #
    wph
    @66
    @71
    wi
    #
    @47
    @52
    wph
    @29
    cF
    wfun
    #
    @73
    fmfnfm.f
    cY
    cX
    cF
    ffun
    #
    @74
    @66
    @71
    vy
    @43
    @42
    cF
    fvelima
    ex
    3syl
    ad2antrr
    @53
    @70
    @72
    vy
    @42
    @53
    @68
    @42
    wcel
    #
    wa
    #
    @69
    @0
    wcel
    #
    @55
    wi
    @70
    @72
    @77
    @78
    @68
    @1
    wcel
    #
    @55
    @77
    @74
    @68
    cF
    cdm
    #
    wcel
    @78
    @79
    wb
    wph
    @74
    @47
    @52
    @76
    wph
    @29
    @74
    fmfnfm.f
    @75
    syl
    ad3antrrr
    @53
    @42
    @80
    @68
    @51
    @42
    @80
    wss
    @52
    @51
    @42
    cY
    @80
    wph
    @24
    @47
    @42
    cY
    wss
    fmfnfm.b
    cY
    cB
    @42
    fbelss
    sylan
    wph
    @80
    cY
    wceq
    #
    @47
    wph
    @29
    @81
    fmfnfm.f
    cY
    cX
    cF
    fdm
    syl
    adantr
    sseqtr4d
    adantr
    sselda
    @68
    @0
    cF
    fvimacnv
    syl2anc
    @76
    @79
    @55
    wi
    @53
    @76
    @79
    @55
    @68
    @42
    @1
    inelcm
    ex
    adantl
    sylbid
    @70
    @78
    @67
    @55
    @69
    @43
    @0
    eleq1
    imbi1d
    syl5ibcom
    rexlimdva
    syld
    impd
    syl5bi
    exlimdv
    syl5bi
    mpd
    @49
    @44
    @54
    c0
    @43
    @1
    @42
    ineq2
    neeq1d
    syl5ibrcom
    rexlimdva
    syl5bi
    expimpd
    ralrimivv
    wph
    @24
    @25
    @23
    @46
    wb
    fmfnfm.b
    @40
    vs
    vt
    cB
    @3
    cY
    cY
    fbunfip
    syl2anc
    mpbird
    wph
    @24
    @27
    @19
    @21
    @22
    @23
    w3a
    wb
    fmfnfm.b
    @31
    @4
    @26
    cY
    fsubbas
    3syl
    mpbir3and
    #
    @5
    cY
    fgcl
    syl
    wph
    cB
    @5
    @6
    wph
    cB
    @3
    @5
    wph
    @4
    cvv
    wcel
    #
    @4
    @5
    wss
    wph
    @24
    @25
    @83
    fmfnfm.b
    @40
    cB
    @3
    @18
    @18
    unexg
    syl2anc
    @4
    cvv
    ssfii
    syl
    unssad
    wph
    @19
    @5
    @6
    wss
    @82
    @5
    cY
    ssfg
    syl
    sstrd
    wph
    cL
    @5
    @10
    cfv
    #
    @11
    wph
    vt
    cL
    @84
    wph
    @43
    cL
    wcel
    @43
    cX
    wss
    @56
    @43
    wss
    vs
    @5
    wrex
    wa
    #
    @43
    @84
    wcel
    #
    wph
    vx
    vt
    cB
    cF
    cL
    cX
    cY
    vs
    fmfnfm.b
    fmfnfm.l
    fmfnfm.f
    fmfnfm.fm
    fmfnfmlem4
    wph
    @35
    @19
    @29
    @86
    @85
    wb
    @38
    @82
    fmfnfm.f
    vs
    @43
    @5
    cL
    cF
    cX
    cY
    elfm
    syl3anc
    bitr4d
    eqrdv
    wph
    @35
    @19
    @29
    @84
    @11
    wceq
    @38
    @82
    fmfnfm.f
    @5
    cL
    cF
    @6
    cX
    cY
    @6
    eqid
    fmfg
    syl3anc
    eqtrd
    @17
    @9
    @12
    wa
    vf
    @6
    @7
    @13
    @6
    wceq
    #
    @14
    @9
    @16
    @12
    @13
    @6
    cB
    sseq2
    @87
    @15
    @11
    cL
    @13
    @6
    @10
    fveq2
    eqeq2d
    anbi12d
    rspcev
    syl12anc
end
