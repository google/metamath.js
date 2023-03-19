include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "crest.mm"
include "co.mm"
include "cnei.mm"
include "cfv.mm"
include "cv.mm"
include "cuni.mm"
include "wa.mm"
include "wrex.mm"
include "cin.mm"
include "wceq.mm"
include "wex.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "simpl.mm"
include "anim2i.mm"
include "cdif.mm"
include "cun.mm"
include "simp-5r.mm"
include "simp1.mm"
include "simp2.mm"
include "restuni.mm"
include "syl2anc.mm"
include "ad5antr.mm"
include "sseqtr4d.mm"
include "sstrd.mm"
include "simplr.mm"
include "eltopss.mm"
include "ssdifssd.mm"
include "unssd.mm"
include "simpr1l.mm"
include "3anassrs.mm"
include "simpr.mm"
include "sseqtrd.mm"
include "inss1.mm"
include "syl6ss.mm"
include "inundif.mm"
include "simpr1r.mm"
include "eqsstr3d.mm"
include "unss1.mm"
include "syl.mm"
include "syl5eqssr.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "c0.mm"
include "indir.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtr3i.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "df-ss.mm"
include "biimpi.mm"
include "syl5req.mm"
include "vex.mm"
include "cvv.mm"
include "difexg.mm"
include "ax-mp.mm"
include "unex.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "spcev.mm"
include "syl21anc.mm"
include "ad3antrrr.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "ssexd.mm"
include "elrest.mm"
include "biimpa.mm"
include "r19.29a.mm"
include "sylanl1.mm"
include "simprr.mm"
include "r19.29af.mm"
include "inss2.mm"
include "mpbiri.mm"
include "adantl.mm"
include "exlimiv.mm"
include "adantr.mm"
include "ad4antr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "simprl.mm"
include "simp3.mm"
include "ssind.mm"
include "ssrin.mm"
include "simp-4r.mm"
include "jca32.mm"
include "ex.mm"
include "reximdva.mm"
include "impr.mm"
include "an32s.mm"
include "expl.mm"
include "exlimdv.mm"
include "imp.mm"
include "rexlimivw.mm"
include "jca.mm"
include "impbida.mm"
include "wb.mm"
include "resttop.mm"
include "eqid.mm"
include "isnei.mm"
include "cmpt.mm"
include "crn.mm"
include "fvex.mm"
include "restval.mm"
include "sylancr.mm"
include "eleq2d.mm"
include "elrnmpt.mm"
include "df-rex.mm"
include "bitri.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem neitr
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  assume neitr.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X /\ B C_ A ) -> ( ( nei ` ( J |`t A ) ) ` B ) = ( ( ( nei ` J ) ` B ) |`t A ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    cB
    cA
    wss
    #
    w3a
    #
    vc
    cB
    cJ
    cA
    crest
    co
    #
    cnei
    cfv
    cfv
    #
    cB
    cJ
    cnei
    cfv
    #
    cfv
    #
    cA
    crest
    co
    #
    @3
    vc
    cv
    #
    @4
    cuni
    #
    wss
    #
    cB
    vd
    cv
    #
    wss
    #
    @12
    @9
    wss
    #
    wa
    #
    vd
    @4
    wrex
    #
    wa
    #
    va
    cv
    #
    cX
    wss
    #
    cB
    vb
    cv
    #
    wss
    #
    @20
    @18
    wss
    #
    wa
    #
    vb
    cJ
    wrex
    #
    wa
    #
    @9
    @18
    cA
    cin
    #
    wceq
    #
    wa
    #
    va
    wex
    #
    @9
    @5
    wcel
    #
    @9
    @8
    wcel
    #
    @3
    @17
    @29
    @3
    @17
    wa
    #
    @15
    @29
    vd
    @4
    @3
    @17
    vd
    @3
    vd
    nfv
    @11
    @16
    vd
    @11
    vd
    nfv
    @15
    vd
    @4
    nfre1
    nfan
    nfan
    @32
    @3
    @11
    wa
    #
    @12
    @4
    wcel
    #
    @15
    @29
    @17
    @11
    @3
    @11
    @16
    simpl
    anim2i
    @33
    @34
    wa
    #
    @15
    wa
    #
    @12
    ve
    cv
    #
    cA
    cin
    #
    wceq
    #
    @29
    ve
    cJ
    @36
    @37
    cJ
    wcel
    #
    wa
    #
    @39
    wa
    #
    @9
    @37
    cA
    cdif
    #
    cun
    #
    cX
    wss
    #
    @21
    @20
    @44
    wss
    #
    wa
    #
    vb
    cJ
    wrex
    #
    @9
    @44
    cA
    cin
    #
    wceq
    #
    @29
    @42
    @9
    @43
    cX
    @42
    @9
    cA
    cX
    @42
    @9
    @10
    cA
    @3
    @11
    @34
    @15
    @40
    @39
    simp-5r
    @3
    cA
    @10
    wceq
    #
    @11
    @34
    @15
    @40
    @39
    @3
    @0
    @1
    @51
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    cA
    cJ
    cX
    neitr.1
    restuni
    syl2anc
    #
    ad5antr
    sseqtr4d
    #
    @3
    @1
    @11
    @34
    @15
    @40
    @39
    @53
    ad5antr
    sstrd
    @42
    @37
    cX
    cA
    @42
    @0
    @40
    @37
    cX
    wss
    @3
    @0
    @11
    @34
    @15
    @40
    @39
    @52
    ad5antr
    @36
    @40
    @39
    simplr
    #
    @37
    cJ
    cX
    neitr.1
    eltopss
    syl2anc
    ssdifssd
    unssd
    @42
    @40
    cB
    @37
    wss
    #
    @37
    @44
    wss
    #
    @48
    @56
    @42
    cB
    @38
    @37
    @42
    cB
    @12
    @38
    @35
    @15
    @40
    @39
    @13
    @13
    @14
    @40
    @39
    @35
    simpr1l
    3anassrs
    @41
    @39
    simpr
    #
    sseqtrd
    @37
    cA
    inss1
    syl6ss
    @42
    @37
    @38
    @43
    cun
    #
    @44
    @37
    cA
    inundif
    @42
    @38
    @9
    wss
    @60
    @44
    wss
    @42
    @38
    @12
    @9
    @59
    @35
    @15
    @40
    @39
    @14
    @13
    @14
    @40
    @39
    @35
    simpr1r
    3anassrs
    eqsstr3d
    @38
    @9
    @43
    unss1
    syl
    syl5eqssr
    @47
    @57
    @58
    wa
    vb
    @37
    cJ
    @20
    @37
    wceq
    @21
    @57
    @46
    @58
    @20
    @37
    cB
    sseq2
    @20
    @37
    @44
    sseq1
    anbi12d
    rspcev
    syl12anc
    @42
    @9
    cA
    wss
    #
    @50
    @55
    @61
    @49
    @9
    cA
    cin
    #
    @9
    @49
    @62
    @43
    cA
    cin
    #
    cun
    @62
    c0
    cun
    @62
    @9
    @43
    cA
    indir
    @63
    c0
    @62
    cA
    @43
    cin
    @63
    c0
    cA
    @43
    incom
    cA
    @37
    disjdif
    eqtr3i
    uneq2i
    @62
    un0
    3eqtri
    @61
    @62
    @9
    wceq
    @9
    cA
    df-ss
    biimpi
    syl5req
    syl
    @28
    @45
    @48
    wa
    #
    @50
    wa
    va
    @44
    @9
    @43
    vc
    vex
    #
    @37
    cvv
    wcel
    @43
    cvv
    wcel
    ve
    vex
    @37
    cA
    cvv
    difexg
    ax-mp
    unex
    @18
    @44
    wceq
    #
    @25
    @64
    @27
    @50
    @66
    @19
    @45
    @24
    @48
    @18
    @44
    cX
    sseq1
    @66
    @23
    @47
    vb
    cJ
    @66
    @22
    @46
    @21
    @18
    @44
    @20
    sseq2
    anbi2d
    rexbidv
    anbi12d
    @66
    @26
    @49
    @9
    @18
    @44
    cA
    ineq1
    eqeq2d
    anbi12d
    spcev
    syl21anc
    @36
    @0
    cA
    cvv
    wcel
    #
    @34
    @39
    ve
    cJ
    wrex
    #
    @3
    @0
    @11
    @34
    @15
    @52
    ad3antrrr
    @3
    @67
    @11
    @34
    @15
    @3
    cA
    cX
    cvv
    @3
    cX
    cJ
    cuni
    #
    cvv
    neitr.1
    @3
    @0
    @69
    cvv
    wcel
    @52
    cJ
    ctop
    uniexg
    syl
    syl5eqel
    @53
    ssexd
    #
    ad3antrrr
    @33
    @34
    @15
    simplr
    @0
    @67
    wa
    @34
    @68
    ve
    @12
    cA
    cJ
    ctop
    cvv
    elrest
    biimpa
    syl21anc
    r19.29a
    sylanl1
    @3
    @11
    @16
    simprr
    r19.29af
    @3
    @29
    wa
    #
    @11
    @16
    @71
    @9
    cA
    @10
    @29
    @61
    @3
    @28
    @61
    va
    @27
    @61
    @25
    @27
    @61
    @26
    cA
    wss
    @18
    cA
    inss2
    @9
    @26
    cA
    sseq1
    mpbiri
    adantl
    exlimiv
    adantl
    @3
    @51
    @29
    @54
    adantr
    sseqtrd
    @71
    @20
    cA
    cin
    #
    @4
    wcel
    #
    cB
    @72
    wss
    #
    @72
    @9
    wss
    #
    wa
    #
    wa
    #
    vb
    cJ
    wrex
    #
    @16
    @3
    @29
    @78
    @3
    @28
    @78
    va
    @3
    @25
    @27
    @78
    @3
    @27
    @25
    @78
    @3
    @27
    wa
    #
    @19
    @24
    @78
    @79
    @19
    wa
    #
    @23
    @77
    vb
    cJ
    @80
    @20
    cJ
    wcel
    #
    wa
    #
    @23
    @77
    @82
    @23
    wa
    #
    @73
    @74
    @75
    @83
    @0
    @67
    @81
    @73
    @3
    @0
    @27
    @19
    @81
    @23
    @52
    ad4antr
    @3
    @67
    @27
    @19
    @81
    @23
    @70
    ad4antr
    @80
    @81
    @23
    simplr
    @20
    cA
    cJ
    ctop
    cvv
    elrestr
    syl3anc
    @83
    cB
    @20
    cA
    @82
    @21
    @22
    simprl
    @3
    @2
    @27
    @19
    @81
    @23
    @0
    @1
    @2
    simp3
    #
    ad4antr
    ssind
    @83
    @72
    @26
    @9
    @83
    @22
    @72
    @26
    wss
    @82
    @21
    @22
    simprr
    @20
    @18
    cA
    ssrin
    syl
    @3
    @27
    @19
    @81
    @23
    simp-4r
    sseqtr4d
    jca32
    ex
    reximdva
    impr
    an32s
    expl
    exlimdv
    imp
    @77
    @16
    vb
    cJ
    @15
    @76
    vd
    @72
    @4
    @12
    @72
    wceq
    @13
    @74
    @14
    @75
    @12
    @72
    cB
    sseq2
    @12
    @72
    @9
    sseq1
    anbi12d
    rspcev
    rexlimivw
    syl
    jca
    impbida
    @3
    @4
    ctop
    wcel
    #
    cB
    @10
    wss
    @30
    @17
    wb
    @3
    @0
    @67
    @85
    @52
    @70
    cA
    cJ
    cvv
    resttop
    syl2anc
    @3
    cB
    cA
    @10
    @84
    @54
    sseqtrd
    cB
    vd
    @4
    @9
    @10
    @10
    eqid
    isnei
    syl2anc
    @3
    @31
    @9
    va
    @7
    @26
    cmpt
    #
    crn
    #
    wcel
    #
    @29
    @3
    @8
    @87
    @9
    @3
    @7
    cvv
    wcel
    @67
    @8
    @87
    wceq
    cB
    @6
    fvex
    @70
    va
    cA
    @7
    cvv
    cvv
    restval
    sylancr
    eleq2d
    @3
    @0
    cB
    cX
    wss
    #
    @88
    @29
    wb
    @52
    @3
    cB
    cA
    cX
    @84
    @53
    sstrd
    @88
    @18
    @7
    wcel
    #
    @27
    wa
    #
    va
    wex
    #
    @0
    @89
    wa
    #
    @29
    @88
    @27
    va
    @7
    wrex
    #
    @92
    @9
    cvv
    wcel
    @88
    @94
    wb
    @65
    va
    @7
    @26
    @9
    @86
    cvv
    @86
    eqid
    elrnmpt
    ax-mp
    @27
    va
    @7
    df-rex
    bitri
    @93
    @91
    @28
    va
    @93
    @90
    @25
    @27
    cB
    vb
    cJ
    @18
    cX
    neitr.1
    isnei
    anbi1d
    exbidv
    syl5bb
    syl2anc
    bitrd
    3bitr4d
    eqrdv
end
