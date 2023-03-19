include "cqtop.mm"
include "co.mm"
include "ctop.mm"
include "wcel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "ctx.mm"
include "ccld.mm"
include "cfv.mm"
include "cha.mm"
include "wfn.mm"
include "haustop.mm"
include "syl.mm"
include "wfo.mm"
include "fofn.mm"
include "qtoptop.mm"
include "syl2anc.mm"
include "wss.mm"
include "cdif.mm"
include "txtop.mm"
include "cxp.mm"
include "idssxp.mm"
include "wceq.mm"
include "eqid.mm"
include "txuni.mm"
include "syl5sseq.mm"
include "qtopuni.mm"
include "sqxpeqd.mm"
include "eqtr2d.mm"
include "eqcomd.mm"
include "reseq2d.mm"
include "difeq12d.mm"
include "cima.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "cop.mm"
include "wbr.mm"
include "wn.mm"
include "simp-4r.mm"
include "simplr.mm"
include "opelxpi.mm"
include "df-br.mm"
include "sylibr.mm"
include "wne.mm"
include "simpllr.mm"
include "simpr.mm"
include "opeq12d.mm"
include "simp-5r.mm"
include "simp-8r.mm"
include "eqeltrrd.mm"
include "eqeltrd.mm"
include "wrel.mm"
include "wb.mm"
include "relxp.mm"
include "opeldifid.mm"
include "ax-mp.mm"
include "sylib.mm"
include "simprd.mm"
include "ad8antr.mm"
include "fcoinvbr.mm"
include "syl3anc.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "brdif.mm"
include "bitr3i.mm"
include "sylanbrc.mm"
include "fvproj.mm"
include "3eqtr4d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "wfun.mm"
include "fofun.mm"
include "ad4antr.mm"
include "ad2antrr.mm"
include "foima.mm"
include "eleqtrrd.mm"
include "fvelima.mm"
include "r19.29a.mm"
include "eldifad.mm"
include "elxp2.mm"
include "r19.29vva.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "wf.mm"
include "fof.mm"
include "ad5antr.mm"
include "ffvelrnd.mm"
include "opelxp.mm"
include "simprbi.mm"
include "mpbid.mm"
include "eldifi.mm"
include "adantl.mm"
include "adantr.mm"
include "r19.29an.mm"
include "impbida.mm"
include "opex.mm"
include "fnmpt2i.mm"
include "difss.mm"
include "fvelimab.mm"
include "mp2an.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"
include "cvv.mm"
include "ssv.mm"
include "xpss2.mm"
include "difres.mm"
include "mp2b.mm"
include "syl6eqr.mm"
include "ctopon.mm"
include "toptopon.mm"
include "qtoptopon.mm"
include "wral.mm"
include "ralrimiva.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "r19.21bi.mm"
include "difeq1d.mm"
include "wer.mm"
include "ccnv.mm"
include "ccom.mm"
include "fcoinver.mm"
include "ereq1.mm"
include "erssxp.mm"
include "sseqtrd.mm"
include "iscld2.mm"
include "txomap.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "hausdiag.mm"

theorem qtophaus
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.sm: class .~
  let cF: class F
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  assume qtophaus.x: |- X = U. J
  assume qtophaus.e: |- .~ = ( `' F o. F )
  assume qtophaus.h: |- H = ( x e. X , y e. X |-> <. ( F ` x ) , ( F ` y ) >. )
  assume qtophaus.1: |- ( ph -> J e. Haus )
  assume qtophaus.2: |- ( ph -> F : X -onto-> Y )
  assume qtophaus.3: |- ( ( ph /\ x e. J ) -> ( F " x ) e. ( J qTop F ) )
  assume qtophaus.4: |- ( ph -> .~ e. ( Clsd ` ( J tX J ) ) )

  disjoint .~ x
  disjoint .~ y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint .~ a
  disjoint .~ b
  disjoint .~ c
  disjoint .~ z
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint x z
  disjoint y z
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X z
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint ph z
  assert |- ( ph -> ( J qTop F ) e. Haus )

  proof
    wph
    cJ
    cF
    cqtop
    co
    #
    ctop
    wcel
    #
    cid
    @0
    cuni
    #
    cres
    #
    @0
    @0
    ctx
    co
    #
    ccld
    cfv
    wcel
    #
    @0
    cha
    wcel
    wph
    cJ
    ctop
    wcel
    #
    cF
    cX
    wfn
    #
    @1
    wph
    cJ
    cha
    wcel
    @6
    qtophaus.1
    cJ
    haustop
    syl
    #
    wph
    cX
    cY
    cF
    wfo
    #
    @7
    qtophaus.2
    cX
    cY
    cF
    fofn
    syl
    #
    cF
    cJ
    cX
    qtophaus.x
    qtoptop
    syl2anc
    #
    wph
    @4
    ctop
    wcel
    #
    @3
    @4
    cuni
    #
    wss
    #
    @13
    @3
    cdif
    #
    @4
    wcel
    #
    @5
    wph
    @1
    @1
    @12
    @11
    @11
    @0
    @0
    txtop
    syl2anc
    wph
    @2
    @2
    cxp
    #
    @3
    @13
    @2
    idssxp
    wph
    @1
    @1
    @17
    @13
    wceq
    @11
    @11
    @0
    @0
    @2
    @2
    @2
    eqid
    #
    @18
    txuni
    syl2anc
    #
    syl5sseq
    wph
    @15
    cY
    cY
    cxp
    #
    cid
    cY
    cres
    #
    cdif
    #
    @4
    wph
    @13
    @20
    @3
    @21
    wph
    @20
    @17
    @13
    wph
    cY
    @2
    wph
    @6
    @9
    cY
    @2
    wceq
    @8
    qtophaus.2
    cF
    cJ
    cX
    cY
    qtophaus.x
    qtopuni
    syl2anc
    #
    sqxpeqd
    @19
    eqtr2d
    wph
    @2
    cY
    cid
    wph
    cY
    @2
    @23
    eqcomd
    reseq2d
    difeq12d
    wph
    cH
    cX
    cX
    cxp
    #
    c.sm
    cdif
    #
    cima
    #
    @22
    @4
    wph
    @26
    @20
    cid
    cdif
    #
    @22
    wph
    vc
    @26
    @27
    wph
    vc
    cv
    #
    @27
    wcel
    #
    vz
    cv
    #
    cH
    cfv
    #
    @28
    wceq
    #
    vz
    @25
    wrex
    #
    @28
    @26
    wcel
    #
    wph
    @29
    @33
    wph
    @29
    wa
    #
    @28
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    @33
    va
    vb
    cY
    cY
    @35
    @36
    cY
    wcel
    #
    wa
    #
    @37
    cY
    wcel
    #
    wa
    #
    @39
    wa
    #
    vx
    cv
    #
    cF
    cfv
    #
    @36
    wceq
    #
    @33
    vx
    cX
    @44
    @45
    cX
    wcel
    #
    wa
    #
    @47
    wa
    #
    vy
    cv
    #
    cF
    cfv
    #
    @37
    wceq
    #
    @33
    vy
    cX
    @50
    @51
    cX
    wcel
    #
    wa
    #
    @53
    wa
    #
    @45
    @51
    cop
    #
    @25
    wcel
    #
    @57
    cH
    cfv
    #
    @28
    wceq
    #
    @33
    @56
    @45
    @51
    @24
    wbr
    #
    @45
    @51
    c.sm
    wbr
    #
    wn
    #
    @58
    @56
    @57
    @24
    wcel
    #
    @61
    @56
    @48
    @54
    @64
    @44
    @48
    @47
    @54
    @53
    simp-4r
    #
    @50
    @54
    @53
    simplr
    #
    @45
    @51
    cX
    cX
    opelxpi
    syl2anc
    @45
    @51
    @24
    df-br
    sylibr
    @56
    @63
    @46
    @52
    wne
    #
    @56
    @46
    @52
    cop
    #
    @20
    wcel
    #
    @67
    @56
    @68
    @27
    wcel
    #
    @69
    @67
    wa
    #
    @56
    @68
    @38
    @27
    @56
    @46
    @36
    @52
    @37
    @49
    @47
    @54
    @53
    simpllr
    @55
    @53
    simpr
    opeq12d
    #
    @56
    @28
    @38
    @27
    @43
    @39
    @48
    @47
    @54
    @53
    simp-5r
    #
    wph
    @29
    @40
    @42
    @39
    @48
    @47
    @54
    @53
    simp-8r
    eqeltrrd
    eqeltrd
    @20
    wrel
    @70
    @71
    wb
    cY
    cY
    relxp
    @20
    @46
    @52
    opeldifid
    ax-mp
    #
    sylib
    simprd
    @56
    @62
    @46
    @52
    @56
    @7
    @48
    @54
    @62
    @46
    @52
    wceq
    wb
    #
    wph
    @7
    @29
    @40
    @42
    @39
    @48
    @47
    @54
    @53
    @10
    ad8antr
    @65
    @66
    cX
    c.sm
    cF
    @45
    @51
    qtophaus.e
    fcoinvbr
    #
    syl3anc
    necon3bbid
    mpbird
    @58
    @45
    @51
    @25
    wbr
    @61
    @63
    wa
    @45
    @51
    @25
    df-br
    @45
    @51
    @24
    c.sm
    brdif
    bitr3i
    #
    sylanbrc
    @56
    @68
    @38
    @59
    @28
    @72
    @56
    vx
    vy
    cX
    cX
    cF
    cF
    cH
    @45
    @51
    qtophaus.h
    @65
    @66
    fvproj
    @73
    3eqtr4d
    @32
    @60
    vz
    @57
    @25
    @30
    @57
    wceq
    #
    @31
    @59
    @28
    @30
    @57
    cH
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @50
    cF
    wfun
    #
    @37
    cF
    cX
    cima
    #
    wcel
    @53
    vy
    cX
    wrex
    @44
    @79
    @48
    @47
    wph
    @79
    @29
    @40
    @42
    @39
    wph
    @9
    @79
    qtophaus.2
    cX
    cY
    cF
    fofun
    syl
    ad4antr
    #
    ad2antrr
    @50
    @37
    cY
    @80
    @41
    @42
    @39
    @48
    @47
    simp-4r
    @44
    @80
    cY
    wceq
    #
    @48
    @47
    wph
    @82
    @29
    @40
    @42
    @39
    wph
    @9
    @82
    qtophaus.2
    cX
    cY
    cF
    foima
    syl
    ad4antr
    #
    ad2antrr
    eleqtrrd
    vy
    @37
    cX
    cF
    fvelima
    syl2anc
    r19.29a
    @44
    @79
    @36
    @80
    wcel
    @47
    vx
    cX
    wrex
    @81
    @44
    @36
    cY
    @80
    @35
    @40
    @42
    @39
    simpllr
    @83
    eleqtrrd
    vx
    @36
    cX
    cF
    fvelima
    syl2anc
    r19.29a
    @35
    @28
    @20
    wcel
    @39
    vb
    cY
    wrex
    va
    cY
    wrex
    @35
    @28
    @20
    cid
    wph
    @29
    simpr
    eldifad
    va
    vb
    @28
    cY
    cY
    elxp2
    sylib
    r19.29vva
    wph
    @32
    @29
    vz
    @25
    wph
    @30
    @25
    wcel
    #
    wa
    #
    @32
    wa
    #
    @78
    @29
    vx
    vy
    cX
    cX
    @86
    @48
    wa
    #
    @54
    wa
    #
    @78
    wa
    #
    @28
    @68
    @27
    @89
    @31
    @59
    @28
    @68
    @89
    @30
    @57
    cH
    @88
    @78
    simpr
    #
    fveq2d
    @85
    @32
    @48
    @54
    @78
    simp-4r
    @89
    vx
    vy
    cX
    cX
    cF
    cF
    cH
    @45
    @51
    qtophaus.h
    @86
    @48
    @54
    @78
    simpllr
    #
    @87
    @54
    @78
    simplr
    #
    fvproj
    3eqtr3d
    @89
    @69
    @67
    @70
    @89
    @46
    cY
    wcel
    @52
    cY
    wcel
    @69
    @89
    cX
    cY
    @45
    cF
    wph
    cX
    cY
    cF
    wf
    #
    @84
    @32
    @48
    @54
    @78
    wph
    @9
    @93
    qtophaus.2
    cX
    cY
    cF
    fof
    syl
    #
    ad5antr
    #
    @91
    ffvelrnd
    @89
    cX
    cY
    @51
    cF
    @95
    @92
    ffvelrnd
    @46
    @52
    cY
    cY
    opelxp
    sylanbrc
    @89
    @63
    @67
    @89
    @58
    @63
    @89
    @30
    @57
    @25
    @90
    wph
    @84
    @32
    @48
    @54
    @78
    simp-5r
    eqeltrrd
    @58
    @61
    @63
    @77
    simprbi
    syl
    @89
    @62
    @46
    @52
    @89
    @7
    @48
    @54
    @75
    wph
    @7
    @84
    @32
    @48
    @54
    @78
    @10
    ad5antr
    @91
    @92
    @76
    syl3anc
    necon3bbid
    mpbid
    @74
    sylanbrc
    eqeltrd
    @85
    @78
    vy
    cX
    wrex
    vx
    cX
    wrex
    #
    @32
    @85
    @30
    @24
    wcel
    #
    @96
    @84
    @97
    wph
    @30
    @24
    c.sm
    eldifi
    adantl
    vx
    vy
    @30
    cX
    cX
    elxp2
    sylib
    adantr
    r19.29vva
    r19.29an
    impbida
    cH
    @24
    wfn
    @25
    @24
    wss
    @34
    @33
    wb
    vx
    vy
    cX
    cX
    @68
    cH
    qtophaus.h
    @46
    @52
    opex
    fnmpt2i
    @24
    c.sm
    difss
    vz
    @24
    @25
    @28
    cH
    fvelimab
    mp2an
    syl6rbbr
    eqrdv
    cY
    cvv
    wss
    @20
    cY
    cvv
    cxp
    wss
    @22
    @27
    wceq
    cY
    ssv
    cY
    cvv
    cY
    xpss2
    @20
    cY
    cid
    difres
    mp2b
    syl6eqr
    wph
    vx
    vy
    @25
    cY
    cF
    cF
    cH
    cJ
    cJ
    @0
    @0
    cX
    cX
    cY
    @94
    @94
    wph
    @6
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @8
    cJ
    cX
    qtophaus.x
    toptopon
    sylib
    #
    @99
    wph
    @98
    @9
    @0
    cY
    ctopon
    cfv
    wcel
    @99
    qtophaus.2
    cF
    cJ
    cX
    cY
    qtoptopon
    syl2anc
    #
    @100
    qtophaus.3
    wph
    cF
    @51
    cima
    #
    @0
    wcel
    #
    vy
    cJ
    wph
    cF
    @45
    cima
    #
    @0
    wcel
    #
    vx
    cJ
    wral
    @102
    vy
    cJ
    wral
    wph
    @104
    vx
    cJ
    qtophaus.3
    ralrimiva
    @104
    @102
    vx
    vy
    cJ
    @45
    @51
    wceq
    @103
    @101
    @0
    @45
    @51
    cF
    imaeq2
    eleq1d
    cbvralv
    sylib
    r19.21bi
    wph
    @25
    cJ
    cJ
    ctx
    co
    #
    cuni
    #
    c.sm
    cdif
    #
    @105
    wph
    @24
    @106
    c.sm
    wph
    @6
    @6
    @24
    @106
    wceq
    @8
    @8
    cJ
    cJ
    cX
    cX
    qtophaus.x
    qtophaus.x
    txuni
    syl2anc
    #
    difeq1d
    wph
    c.sm
    @105
    ccld
    cfv
    wcel
    #
    @107
    @105
    wcel
    #
    qtophaus.4
    wph
    @105
    ctop
    wcel
    #
    c.sm
    @106
    wss
    @109
    @110
    wb
    wph
    @6
    @6
    @111
    @8
    @8
    cJ
    cJ
    txtop
    syl2anc
    wph
    c.sm
    @24
    @106
    wph
    cX
    c.sm
    wer
    #
    c.sm
    @24
    wss
    wph
    cX
    cF
    ccnv
    cF
    ccom
    #
    wer
    #
    @112
    wph
    @7
    @114
    @10
    cF
    cX
    fcoinver
    syl
    c.sm
    @113
    wceq
    @112
    @114
    wb
    qtophaus.e
    cX
    c.sm
    @113
    ereq1
    ax-mp
    sylibr
    cX
    c.sm
    erssxp
    syl
    @108
    sseqtrd
    c.sm
    @105
    @106
    @106
    eqid
    iscld2
    syl2anc
    mpbid
    eqeltrd
    qtophaus.h
    txomap
    eqeltrrd
    eqeltrd
    @12
    @14
    wa
    @5
    @16
    @3
    @4
    @13
    @13
    eqid
    iscld2
    biimpar
    syl21anc
    @0
    @2
    @18
    hausdiag
    sylanbrc
end
