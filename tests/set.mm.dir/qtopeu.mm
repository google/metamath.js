include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "cqtop.mm"
include "co.mm"
include "ccn.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cuni.mm"
include "cmpt.mm"
include "wcel.mm"
include "cfv.mm"
include "wfn.mm"
include "wb.mm"
include "wfo.mm"
include "fofn.mm"
include "syl.mm"
include "adantr.mm"
include "fniniseg.mm"
include "w3a.mm"
include "eqcom.mm"
include "3anbi3i.mm"
include "3anass.mm"
include "bitri.mm"
include "sylan2br.mm"
include "eqcomd.mm"
include "expr.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "wss.mm"
include "wf.mm"
include "ctopon.mm"
include "ctop.mm"
include "cntop2.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffn.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fof.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "eqeq1.mm"
include "ralima.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "simpr.mm"
include "eqidd.mm"
include "mpbir2and.mm"
include "inelcm.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "eqsn.mm"
include "unieqd.mm"
include "fvex.mm"
include "unisn.mm"
include "syl6req.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "ffvelrnda.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "eqcoms.mm"
include "eleq1d.mm"
include "cbvfo.mm"
include "mpbid.mm"
include "fmpt.mm"
include "qtopcn.mm"
include "syl22anc.mm"
include "coeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "eqtr2.mm"
include "qtoptopon.mm"
include "simprl.mm"
include "simprr.mm"
include "cocan2.mm"
include "syl5ib.mm"
include "ralrimivva.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem qtopeu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vw: setvar w
  let cZ: class Z
  assume qtopeu.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume qtopeu.3: |- ( ph -> F : X -onto-> Y )
  assume qtopeu.4: |- ( ph -> G e. ( J Cn K ) )
  assume qtopeu.5: |- ( ( ph /\ ( x e. X /\ y e. X /\ ( F ` x ) = ( F ` y ) ) ) -> ( G ` x ) = ( G ` y ) )

  disjoint f x
  disjoint f y
  disjoint F f
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J f
  disjoint J x
  disjoint K f
  disjoint K x
  disjoint X x
  disjoint X y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint Y f
  disjoint Y x
  disjoint f g
  disjoint f w
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint J g
  disjoint K g
  disjoint K w
  disjoint X w
  disjoint Z x
  disjoint G g
  disjoint G w
  disjoint g ph
  disjoint Y w
  assert |- ( ph -> E! f e. ( ( J qTop F ) Cn K ) G = ( f o. F ) )

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
    cK
    ccn
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
    @0
    @6
    wceq
    #
    wi
    #
    vg
    @4
    wral
    vf
    @4
    wral
    @2
    vf
    @4
    wreu
    wph
    vw
    cY
    cG
    cF
    ccnv
    #
    vw
    cv
    #
    csn
    #
    cima
    #
    cima
    #
    cuni
    #
    cmpt
    #
    @4
    wcel
    #
    cG
    @18
    cF
    ccom
    #
    wceq
    #
    @5
    wph
    @19
    @20
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    wph
    cG
    @20
    @22
    wph
    vx
    cX
    vx
    cv
    #
    cG
    cfv
    #
    cmpt
    vx
    cX
    cG
    @12
    @24
    cF
    cfv
    #
    csn
    #
    cima
    #
    cima
    #
    cuni
    #
    cmpt
    cG
    @20
    wph
    vx
    cX
    @25
    @30
    wph
    @24
    cX
    wcel
    #
    wa
    #
    @30
    @25
    csn
    #
    cuni
    @25
    @32
    @29
    @33
    @32
    @29
    @33
    wceq
    #
    @13
    @25
    wceq
    #
    vw
    @29
    wral
    #
    @32
    @36
    vy
    cv
    #
    cG
    cfv
    #
    @25
    wceq
    #
    vy
    @28
    wral
    #
    @32
    @39
    vy
    @28
    @32
    @37
    @28
    wcel
    #
    @37
    cX
    wcel
    #
    @37
    cF
    cfv
    #
    @26
    wceq
    #
    wa
    #
    @39
    @32
    cF
    cX
    wfn
    #
    @41
    @45
    wb
    wph
    @46
    @31
    wph
    cX
    cY
    cF
    wfo
    #
    @46
    qtopeu.3
    cX
    cY
    cF
    fofn
    syl
    adantr
    #
    cX
    @26
    @37
    cF
    fniniseg
    syl
    wph
    @31
    @45
    @39
    wph
    @31
    @45
    wa
    #
    wa
    @25
    @38
    @49
    wph
    @31
    @42
    @26
    @43
    wceq
    #
    w3a
    #
    @25
    @38
    wceq
    @51
    @31
    @42
    @44
    w3a
    @49
    @50
    @44
    @31
    @42
    @26
    @43
    eqcom
    3anbi3i
    @31
    @42
    @44
    3anass
    bitri
    qtopeu.5
    sylan2br
    eqcomd
    expr
    sylbid
    ralrimiv
    @32
    cG
    cX
    wfn
    #
    @28
    cX
    wss
    @36
    @40
    wb
    wph
    @52
    @31
    wph
    cX
    cK
    cuni
    #
    cG
    wf
    #
    @52
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    @53
    ctopon
    cfv
    wcel
    #
    cG
    @22
    wcel
    #
    @54
    qtopeu.1
    wph
    cK
    ctop
    wcel
    #
    @56
    wph
    @57
    @58
    qtopeu.4
    cG
    cJ
    cK
    cntop2
    syl
    cK
    @53
    @53
    eqid
    toptopon
    sylib
    #
    qtopeu.4
    cG
    cJ
    cK
    cX
    @53
    cnf2
    syl3anc
    #
    cX
    @53
    cG
    ffn
    syl
    adantr
    @32
    cF
    cdm
    #
    @28
    cX
    cF
    @27
    cnvimass
    wph
    @61
    cX
    wceq
    #
    @31
    wph
    cX
    cY
    cF
    wf
    #
    @62
    wph
    @47
    @63
    qtopeu.3
    cX
    cY
    cF
    fof
    syl
    #
    cX
    cY
    cF
    fdm
    syl
    adantr
    syl5sseq
    @35
    @39
    vw
    vy
    cX
    @28
    cG
    @13
    @38
    @25
    eqeq1
    ralima
    syl2anc
    mpbird
    @32
    @29
    c0
    wne
    #
    @34
    @36
    wb
    @32
    cG
    cdm
    #
    @28
    cin
    #
    c0
    wne
    #
    @65
    @32
    @24
    @66
    wcel
    #
    @24
    @28
    wcel
    #
    @68
    wph
    @69
    @31
    wph
    @66
    cX
    @24
    wph
    @54
    @66
    cX
    wceq
    @60
    cX
    @53
    cG
    fdm
    syl
    eleq2d
    biimpar
    @32
    @70
    @31
    @26
    @26
    wceq
    #
    wph
    @31
    simpr
    @32
    @26
    eqidd
    @32
    @46
    @70
    @31
    @71
    wa
    wb
    @48
    cX
    @26
    @24
    cF
    fniniseg
    syl
    mpbir2and
    @24
    @66
    @28
    inelcm
    syl2anc
    @29
    c0
    @67
    c0
    cG
    @28
    imadisj
    necon3bii
    sylibr
    vw
    @29
    @25
    eqsn
    syl
    mpbird
    unieqd
    @25
    @24
    cG
    fvex
    unisn
    syl6req
    #
    mpteq2dva
    wph
    vx
    cX
    @53
    cG
    @60
    feqmptd
    wph
    vx
    vw
    cX
    cY
    @26
    @17
    @30
    cF
    @18
    wph
    cX
    cY
    @24
    cF
    @64
    ffvelrnda
    wph
    vx
    cX
    cY
    cF
    @64
    feqmptd
    wph
    @18
    eqidd
    @13
    @26
    wceq
    #
    @16
    @29
    @73
    @15
    @28
    cG
    @73
    @14
    @27
    @12
    @13
    @26
    sneq
    imaeq2d
    imaeq2d
    unieqd
    #
    fmptco
    3eqtr4d
    #
    qtopeu.4
    eqeltrrd
    wph
    @55
    @56
    @47
    cY
    @53
    @18
    wf
    #
    @19
    @23
    wb
    qtopeu.1
    @59
    qtopeu.3
    wph
    @17
    @53
    wcel
    #
    vw
    cY
    wral
    #
    @76
    wph
    @30
    @53
    wcel
    #
    vx
    cX
    wral
    #
    @78
    wph
    @79
    vx
    cX
    @32
    @25
    @30
    @53
    @72
    wph
    cX
    @53
    @24
    cG
    @60
    ffvelrnda
    eqeltrrd
    ralrimiva
    wph
    @47
    @80
    @78
    wb
    qtopeu.3
    @79
    @77
    vx
    vw
    cX
    cY
    cF
    @26
    @13
    wceq
    @30
    @17
    @53
    @30
    @17
    wceq
    @13
    @26
    @73
    @17
    @30
    @74
    eqcomd
    eqcoms
    eleq1d
    cbvfo
    syl
    mpbid
    vw
    cY
    @53
    @17
    @18
    @18
    eqid
    fmpt
    sylib
    cF
    @18
    cJ
    cK
    cX
    cY
    @53
    qtopcn
    syl22anc
    mpbird
    @75
    @2
    @21
    vf
    @18
    @4
    @0
    @18
    wceq
    @1
    @20
    cG
    @0
    @18
    cF
    coeq1
    eqeq2d
    rspcev
    syl2anc
    wph
    @11
    vf
    vg
    @4
    @4
    @9
    @1
    @7
    wceq
    #
    wph
    @0
    @4
    wcel
    #
    @6
    @4
    wcel
    #
    wa
    #
    wa
    #
    @10
    cG
    @1
    @7
    eqtr2
    @85
    @47
    @0
    cY
    wfn
    #
    @6
    cY
    wfn
    #
    @81
    @10
    wb
    wph
    @47
    @84
    qtopeu.3
    adantr
    @85
    cY
    @53
    @0
    wf
    #
    @86
    @85
    @3
    cY
    ctopon
    cfv
    wcel
    #
    @56
    @82
    @88
    wph
    @89
    @84
    wph
    @55
    @47
    @89
    qtopeu.1
    qtopeu.3
    cF
    cJ
    cX
    cY
    qtoptopon
    syl2anc
    adantr
    #
    wph
    @56
    @84
    @59
    adantr
    #
    wph
    @82
    @83
    simprl
    @0
    @3
    cK
    cY
    @53
    cnf2
    syl3anc
    cY
    @53
    @0
    ffn
    syl
    @85
    cY
    @53
    @6
    wf
    #
    @87
    @85
    @89
    @56
    @83
    @92
    @90
    @91
    wph
    @82
    @83
    simprr
    @6
    @3
    cK
    cY
    @53
    cnf2
    syl3anc
    cY
    @53
    @6
    ffn
    syl
    cX
    cY
    cF
    @0
    @6
    cocan2
    syl3anc
    syl5ib
    ralrimivva
    @2
    @8
    vf
    vg
    @4
    @10
    @1
    @7
    cG
    @0
    @6
    cF
    coeq1
    eqeq2d
    reu4
    sylanbrc
end
