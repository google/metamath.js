include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "ccom.mm"
include "wss.mm"
include "simplll.mm"
include "simplr.mm"
include "eqid.mm"
include "imaeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "adantl.mm"
include "cvv.mm"
include "wb.mm"
include "imaexg.mm"
include "ustuqtoplem.mm"
include "sylan2.mm"
include "mpbird.mm"
include "syl2anc.mm"
include "w3a.mm"
include "simp-5l.mm"
include "simpld.mm"
include "simp-4r.mm"
include "ustimasn.mm"
include "syl3anc.mm"
include "sselda.mm"
include "jca.mm"
include "wbr.mm"
include "wrel.mm"
include "simp-6l.mm"
include "ustrel.mm"
include "elrelimasn.mm"
include "syl.mm"
include "mpbid.mm"
include "simpr.mm"
include "wex.mm"
include "vex.mm"
include "brco.mm"
include "biimpri.mm"
include "19.23bi.mm"
include "simpllr.mm"
include "ssbrd.mm"
include "mpd.mm"
include "simp-5r.mm"
include "ex.mm"
include "ssrdv.mm"
include "adantr.mm"
include "3jca.mm"
include "eqidd.mm"
include "mpdan.mm"
include "syl21anc.mm"
include "wi.mm"
include "sseq2.mm"
include "sseq1.mm"
include "3anbi23d.mm"
include "anbi1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "3anbi2d.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "3anbi1d.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "ustuqtop1.mm"
include "chvarv.mm"
include "vtoclg.mm"
include "impcom.mm"
include "ralrimiva.mm"
include "raleq.mm"
include "ustexhalf.mm"
include "adantlr.mm"
include "r19.29a.mm"
include "rexralbidv.mm"
include "adantllr.mm"
include "biimpa.mm"

theorem ustuqtop4
  let vv: setvar v
  let cU: class U
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cA: class A
  let vw: setvar w
  let cP: class P
  let vc: setvar c
  let vj: setvar j
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  assume utopustuq.1: |- N = ( p e. X |-> ran ( v e. U |-> ( v " { p } ) ) )

  disjoint q v
  disjoint p q
  disjoint p v
  disjoint U p
  disjoint U q
  disjoint U v
  disjoint X p
  disjoint X q
  disjoint X v
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint N a
  disjoint b p
  disjoint b q
  disjoint N b
  disjoint N p
  disjoint N q
  disjoint a v
  disjoint U a
  disjoint b v
  disjoint U b
  disjoint X a
  disjoint X b
  disjoint A w
  disjoint q w
  disjoint P q
  disjoint v w
  disjoint P v
  disjoint P w
  disjoint p w
  disjoint U w
  disjoint a c
  disjoint a j
  disjoint a r
  disjoint a u
  disjoint a w
  disjoint b c
  disjoint b j
  disjoint b r
  disjoint b u
  disjoint b w
  disjoint c j
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c u
  disjoint c w
  disjoint N c
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint j u
  disjoint j w
  disjoint N j
  disjoint p r
  disjoint p u
  disjoint q r
  disjoint q u
  disjoint r u
  disjoint r w
  disjoint N r
  disjoint u w
  disjoint N u
  disjoint N w
  disjoint a x
  disjoint b x
  disjoint j v
  disjoint j x
  disjoint U j
  disjoint p x
  disjoint q x
  disjoint r v
  disjoint r x
  disjoint U r
  disjoint u v
  disjoint u x
  disjoint U u
  disjoint v x
  disjoint w x
  disjoint U x
  disjoint c v
  disjoint X c
  disjoint X j
  disjoint X r
  disjoint X u
  disjoint X w
  assert |- ( ( ( U e. ( UnifOn ` X ) /\ p e. X ) /\ a e. ( N ` p ) ) -> E. b e. ( N ` p ) A. q e. b a e. ( N ` q ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    vp
    cv
    #
    cX
    wcel
    #
    wa
    #
    va
    cv
    #
    @1
    cN
    cfv
    #
    wcel
    #
    wa
    @4
    vw
    cv
    #
    @1
    csn
    #
    cima
    #
    wceq
    #
    @4
    vq
    cv
    #
    cN
    cfv
    #
    wcel
    #
    vq
    vb
    cv
    #
    wral
    vb
    @5
    wrex
    #
    vw
    cU
    @3
    @7
    cU
    wcel
    #
    @10
    @15
    @6
    @3
    @16
    wa
    #
    @10
    wa
    @15
    @9
    @12
    wcel
    #
    vq
    @14
    wral
    #
    vb
    @5
    wrex
    #
    @17
    @20
    @10
    @17
    vu
    cv
    #
    @21
    ccom
    #
    @7
    wss
    #
    @20
    vu
    cU
    @17
    @21
    cU
    wcel
    #
    wa
    #
    @23
    wa
    #
    @21
    @8
    cima
    #
    @5
    wcel
    #
    @18
    vq
    @27
    wral
    #
    @20
    @26
    @3
    @24
    @28
    @3
    @16
    @24
    @23
    simplll
    #
    @17
    @24
    @23
    simplr
    #
    @3
    @24
    wa
    @28
    @27
    @9
    wceq
    #
    vw
    cU
    wrex
    #
    @24
    @33
    @3
    @24
    @27
    @27
    wceq
    #
    @33
    @27
    eqid
    @32
    @34
    vw
    @21
    cU
    @7
    @21
    wceq
    #
    @9
    @27
    @27
    @7
    @21
    @8
    imaeq1
    eqeq2d
    rspcev
    mpan2
    adantl
    @24
    @3
    @27
    cvv
    wcel
    @28
    @33
    wb
    @21
    @8
    cU
    imaexg
    vw
    vv
    @27
    @1
    cU
    cN
    cvv
    cX
    vp
    utopustuq.1
    ustuqtoplem
    sylan2
    mpbird
    syl2anc
    @26
    @18
    vq
    @27
    @26
    @11
    @27
    wcel
    #
    wa
    #
    @0
    @11
    cX
    wcel
    #
    wa
    #
    @21
    @11
    csn
    #
    cima
    #
    @9
    wss
    #
    @9
    cX
    wss
    #
    w3a
    #
    @41
    @12
    wcel
    #
    wa
    #
    @24
    @16
    @18
    @37
    @44
    @45
    @37
    @39
    @42
    @43
    @37
    @0
    @38
    @0
    @2
    @16
    @24
    @23
    @36
    simp-5l
    #
    @26
    @27
    cX
    @11
    @26
    @0
    @24
    @2
    @27
    cX
    wss
    @26
    @0
    @2
    @30
    simpld
    @31
    @0
    @2
    @16
    @24
    @23
    simp-4r
    #
    @1
    cU
    @21
    cX
    ustimasn
    syl3anc
    sselda
    #
    jca
    @37
    vr
    @41
    @9
    @37
    vr
    cv
    #
    @41
    wcel
    #
    @50
    @9
    wcel
    #
    @37
    @51
    wa
    #
    @52
    @1
    @50
    @7
    wbr
    #
    @53
    @1
    @50
    @22
    wbr
    #
    @54
    @53
    @1
    @11
    @21
    wbr
    #
    @11
    @50
    @21
    wbr
    #
    @55
    @53
    @36
    @56
    @26
    @36
    @51
    simplr
    @53
    @21
    wrel
    #
    @36
    @56
    wb
    @53
    @0
    @24
    @58
    @0
    @2
    @16
    @24
    @23
    @36
    @51
    simp-6l
    #
    @17
    @24
    @23
    @36
    @51
    simp-4r
    cU
    @21
    cX
    ustrel
    syl2anc
    #
    @1
    @11
    @21
    elrelimasn
    syl
    mpbid
    @53
    @51
    @57
    @37
    @51
    simpr
    @53
    @58
    @51
    @57
    wb
    @60
    @11
    @50
    @21
    elrelimasn
    syl
    mpbid
    @56
    @57
    wa
    #
    @55
    vq
    @55
    @61
    vq
    wex
    vq
    @1
    @50
    @21
    @21
    vp
    vex
    vr
    vex
    brco
    biimpri
    19.23bi
    syl2anc
    @53
    @22
    @7
    @1
    @50
    @25
    @23
    @36
    @51
    simpllr
    ssbrd
    mpd
    @53
    @7
    wrel
    #
    @52
    @54
    wb
    @53
    @0
    @16
    @62
    @59
    @3
    @16
    @24
    @23
    @36
    @51
    simp-5r
    cU
    @7
    cX
    ustrel
    syl2anc
    @1
    @50
    @7
    elrelimasn
    syl
    mpbird
    ex
    ssrdv
    @37
    @0
    @16
    @2
    @43
    @47
    @3
    @16
    @24
    @23
    @36
    simp-4r
    #
    @26
    @2
    @36
    @48
    adantr
    @1
    cU
    @7
    cX
    ustimasn
    syl3anc
    3jca
    @37
    @0
    @38
    @24
    @45
    @47
    @49
    @17
    @24
    @23
    @36
    simpllr
    #
    @39
    @24
    wa
    @45
    @41
    @7
    @40
    cima
    #
    wceq
    #
    vw
    cU
    wrex
    #
    @24
    @67
    @39
    @24
    @41
    @41
    wceq
    #
    @67
    @24
    @41
    eqidd
    @66
    @68
    vw
    @21
    cU
    @35
    @65
    @41
    @41
    @7
    @21
    @40
    imaeq1
    eqeq2d
    rspcev
    mpdan
    adantl
    @24
    @39
    @41
    cvv
    wcel
    #
    @45
    @67
    wb
    @21
    @40
    cU
    imaexg
    #
    vw
    vv
    @41
    @11
    cU
    cN
    cvv
    cX
    vp
    utopustuq.1
    ustuqtoplem
    sylan2
    mpbird
    syl21anc
    jca
    @64
    @63
    @16
    @46
    @24
    wa
    #
    @18
    @16
    @9
    cvv
    wcel
    @71
    @18
    wi
    #
    @7
    @8
    cU
    imaexg
    @39
    @41
    @14
    wss
    #
    @14
    cX
    wss
    #
    w3a
    #
    @45
    wa
    #
    @24
    wa
    #
    @14
    @12
    wcel
    #
    wi
    @72
    vb
    @9
    cvv
    @14
    @9
    wceq
    #
    @77
    @71
    @78
    @18
    @79
    @76
    @46
    @24
    @79
    @75
    @44
    @45
    @79
    @73
    @42
    @74
    @43
    @39
    @14
    @9
    @41
    sseq2
    @14
    @9
    cX
    sseq1
    3anbi23d
    anbi1d
    anbi1d
    @14
    @9
    @12
    eleq1
    imbi12d
    @24
    @76
    @78
    @24
    @69
    @76
    @78
    wi
    #
    @70
    @39
    @4
    @14
    wss
    #
    @74
    w3a
    #
    @13
    wa
    #
    @78
    wi
    #
    @80
    va
    @41
    cvv
    @4
    @41
    wceq
    #
    @83
    @76
    @78
    @85
    @82
    @75
    @13
    @45
    @85
    @81
    @73
    @39
    @74
    @4
    @41
    @14
    sseq1
    3anbi2d
    @4
    @41
    @12
    eleq1
    anbi12d
    imbi1d
    @3
    @81
    @74
    w3a
    #
    @6
    wa
    #
    @14
    @5
    wcel
    #
    wi
    @84
    vp
    vq
    @1
    @11
    wceq
    #
    @87
    @83
    @88
    @78
    @89
    @86
    @82
    @6
    @13
    @89
    @3
    @39
    @81
    @74
    @89
    @2
    @38
    @0
    @1
    @11
    cX
    eleq1
    anbi2d
    3anbi1d
    @89
    @5
    @12
    @4
    @1
    @11
    cN
    fveq2
    #
    eleq2d
    anbi12d
    @89
    @5
    @12
    @14
    @90
    eleq2d
    imbi12d
    vv
    cU
    cN
    cX
    vp
    va
    vb
    utopustuq.1
    ustuqtop1
    chvarv
    vtoclg
    syl
    impcom
    vtoclg
    syl
    impcom
    syl21anc
    ralrimiva
    @19
    @29
    vb
    @27
    @5
    @18
    vq
    @14
    @27
    raleq
    rspcev
    syl2anc
    @0
    @16
    @23
    vu
    cU
    wrex
    @2
    vu
    cU
    @7
    cX
    ustexhalf
    adantlr
    r19.29a
    adantr
    @10
    @15
    @20
    wb
    @17
    @10
    @13
    @18
    vb
    vq
    @5
    @14
    @4
    @9
    @12
    eleq1
    rexralbidv
    adantl
    mpbird
    adantllr
    @3
    @6
    @10
    vw
    cU
    wrex
    #
    @3
    @4
    cvv
    wcel
    @6
    @91
    wb
    va
    vex
    vw
    vv
    @4
    @1
    cU
    cN
    cvv
    cX
    vp
    utopustuq.1
    ustuqtoplem
    mpan2
    biimpa
    r19.29a
end
