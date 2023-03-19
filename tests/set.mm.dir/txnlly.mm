include "cnlly.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "nllytop.mm"
include "txtop.mm"
include "syl2an.mm"
include "cxp.mm"
include "wss.mm"
include "eltx.mm"
include "c1st.mm"
include "w3a.mm"
include "c2nd.mm"
include "simpll.mm"
include "simprll.mm"
include "simprrl.mm"
include "xp1st.mm"
include "syl.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "simplr.mm"
include "simprlr.mm"
include "xp2nd.mm"
include "reeanv.mm"
include "wi.mm"
include "cuni.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "simprrr.mm"
include "txopn.mm"
include "syl22anc.mm"
include "cop.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "simprl1.mm"
include "simprr1.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "opnneip.mm"
include "simprl2.mm"
include "simprr2.mm"
include "xpss12.mm"
include "elpwid.mm"
include "elssuni.mm"
include "sstrd.mm"
include "eqid.mm"
include "txuni.mm"
include "sseqtrd.mm"
include "ssnei2.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "elind.mm"
include "txrest.mm"
include "simprl3.mm"
include "simprr3.mm"
include "caovcl.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "anassrs.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "expr.mm"
include "ralimdv.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "isnlly.mm"
include "sylanbrc.mm"

theorem txnlly
  let cA: class A
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume txlly.1: |- ( ( j e. A /\ k e. A ) -> ( j tX k ) e. A )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint R j
  disjoint R k
  disjoint S k
  disjoint a b
  disjoint a j
  disjoint a k
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b j
  disjoint b k
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint j r
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k r
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R u
  disjoint R v
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S r
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ( R e. N-Locally A /\ S e. N-Locally A ) -> ( R tX S ) e. N-Locally A )

  proof
    cR
    cA
    cnlly
    #
    wcel
    #
    cS
    @0
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    ctop
    wcel
    #
    @4
    vz
    cv
    #
    crest
    co
    #
    cA
    wcel
    #
    vz
    vy
    cv
    #
    csn
    #
    @4
    cnei
    cfv
    cfv
    #
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @12
    wral
    #
    vx
    @4
    wral
    @4
    @0
    wcel
    @1
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @5
    @2
    cA
    cR
    nllytop
    #
    cA
    cS
    nllytop
    #
    cR
    cS
    txtop
    syl2an
    #
    @3
    @16
    vx
    @4
    @3
    @12
    @4
    wcel
    @9
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    wcel
    #
    @24
    @12
    wss
    #
    wa
    #
    vv
    cS
    wrex
    vu
    cR
    wrex
    #
    vy
    @12
    wral
    @16
    vu
    vv
    @12
    cR
    cS
    @0
    @0
    vy
    eltx
    @3
    @28
    @15
    vy
    @12
    @3
    @27
    @15
    vu
    vv
    cR
    cS
    @3
    @22
    cR
    wcel
    #
    @23
    cS
    wcel
    #
    wa
    #
    @27
    @15
    @3
    @31
    @27
    wa
    #
    wa
    #
    @9
    c1st
    cfv
    #
    vr
    cv
    #
    wcel
    #
    @35
    va
    cv
    #
    wss
    #
    cR
    @37
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vr
    cR
    wrex
    #
    va
    @22
    cpw
    #
    wrex
    #
    @9
    c2nd
    cfv
    #
    vs
    cv
    #
    wcel
    #
    @46
    vb
    cv
    #
    wss
    #
    cS
    @48
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vs
    cS
    wrex
    #
    vb
    @23
    cpw
    #
    wrex
    #
    @15
    @33
    @1
    @29
    @34
    @22
    wcel
    #
    @44
    @1
    @2
    @32
    simpll
    @3
    @29
    @30
    @27
    simprll
    #
    @33
    @25
    @56
    @3
    @31
    @25
    @26
    simprrl
    #
    @9
    @22
    @23
    xp1st
    syl
    vr
    cA
    @34
    @22
    cR
    va
    nlly2i
    syl3anc
    @33
    @2
    @30
    @45
    @23
    wcel
    #
    @55
    @1
    @2
    @32
    simplr
    #
    @3
    @29
    @30
    @27
    simprlr
    #
    @33
    @25
    @59
    @58
    @9
    @22
    @23
    xp2nd
    syl
    vs
    cA
    @45
    @23
    cS
    vb
    nlly2i
    syl3anc
    @44
    @55
    wa
    @42
    @53
    wa
    #
    vb
    @54
    wrex
    va
    @43
    wrex
    @33
    @15
    @42
    @53
    va
    vb
    @43
    @54
    reeanv
    @33
    @62
    @15
    va
    vb
    @43
    @54
    @62
    @41
    @52
    wa
    #
    vs
    cS
    wrex
    vr
    cR
    wrex
    @33
    @37
    @43
    wcel
    #
    @48
    @54
    wcel
    #
    wa
    #
    wa
    #
    @15
    @41
    @52
    vr
    vs
    cR
    cS
    reeanv
    @67
    @63
    @15
    vr
    vs
    cR
    cS
    @33
    @66
    @35
    cR
    wcel
    #
    @46
    cS
    wcel
    #
    wa
    #
    @63
    @15
    wi
    @33
    @66
    @70
    wa
    #
    wa
    #
    @63
    @15
    @72
    @63
    wa
    #
    @37
    @48
    cxp
    #
    @14
    wcel
    @4
    @74
    crest
    co
    #
    cA
    wcel
    #
    @15
    @73
    @11
    @13
    @74
    @73
    @5
    @35
    @46
    cxp
    #
    @11
    wcel
    #
    @77
    @74
    wss
    #
    @74
    @4
    cuni
    #
    wss
    @74
    @11
    wcel
    @3
    @5
    @32
    @71
    @63
    @21
    ad3antrrr
    #
    @73
    @5
    @77
    @4
    wcel
    #
    @9
    @77
    wcel
    @78
    @81
    @73
    @17
    @18
    @68
    @69
    @82
    @33
    @17
    @71
    @63
    @1
    @17
    @2
    @32
    @19
    ad2antrr
    ad2antrr
    #
    @33
    @18
    @71
    @63
    @33
    @2
    @18
    @60
    @20
    syl
    ad2antrr
    #
    @72
    @68
    @63
    @33
    @66
    @68
    @69
    simprrl
    adantr
    @72
    @69
    @63
    @33
    @66
    @68
    @69
    simprrr
    adantr
    @35
    @46
    cR
    cS
    ctop
    ctop
    txopn
    syl22anc
    @73
    @9
    @34
    @45
    cop
    #
    @77
    @73
    @25
    @9
    @85
    wceq
    @33
    @25
    @71
    @63
    @58
    ad2antrr
    @9
    @22
    @23
    1st2nd2
    syl
    @73
    @36
    @47
    @85
    @77
    wcel
    @36
    @38
    @40
    @52
    @72
    simprl1
    @47
    @49
    @51
    @41
    @72
    simprr1
    @34
    @45
    @35
    @46
    opelxpi
    syl2anc
    eqeltrd
    @9
    @4
    @77
    opnneip
    syl3anc
    @73
    @38
    @49
    @79
    @36
    @38
    @40
    @52
    @72
    simprl2
    @47
    @49
    @51
    @41
    @72
    simprr2
    @35
    @37
    @46
    @48
    xpss12
    syl2anc
    @73
    @74
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    @80
    @73
    @37
    @86
    wss
    @48
    @87
    wss
    @74
    @88
    wss
    @73
    @37
    @22
    @86
    @73
    @37
    @22
    @72
    @64
    @63
    @33
    @64
    @65
    @70
    simprll
    adantr
    #
    elpwid
    #
    @73
    @29
    @22
    @86
    wss
    @33
    @29
    @71
    @63
    @57
    ad2antrr
    @22
    cR
    elssuni
    syl
    sstrd
    @73
    @48
    @23
    @87
    @73
    @48
    @23
    @72
    @65
    @63
    @33
    @64
    @65
    @70
    simprlr
    adantr
    #
    elpwid
    #
    @73
    @30
    @23
    @87
    wss
    @33
    @30
    @71
    @63
    @61
    ad2antrr
    @23
    cS
    elssuni
    syl
    sstrd
    @37
    @86
    @48
    @87
    xpss12
    syl2anc
    @73
    @17
    @18
    @88
    @80
    wceq
    @83
    @84
    cR
    cS
    @86
    @87
    @86
    eqid
    @87
    eqid
    txuni
    syl2anc
    sseqtrd
    @10
    @4
    @74
    @77
    @80
    @80
    eqid
    ssnei2
    syl22anc
    @73
    @74
    @12
    wss
    @74
    @13
    wcel
    @73
    @74
    @24
    @12
    @73
    @37
    @22
    wss
    @48
    @23
    wss
    @74
    @24
    wss
    @90
    @92
    @37
    @22
    @48
    @23
    xpss12
    syl2anc
    @33
    @26
    @71
    @63
    @3
    @31
    @25
    @26
    simprrr
    ad2antrr
    sstrd
    @74
    @12
    vx
    vex
    elpw2
    sylibr
    elind
    @73
    @75
    @39
    @50
    ctx
    co
    #
    cA
    @73
    @17
    @18
    @64
    @65
    @75
    @93
    wceq
    @83
    @84
    @89
    @91
    @37
    @48
    cR
    cS
    ctop
    ctop
    @43
    @54
    txrest
    syl22anc
    @73
    @40
    @51
    @93
    cA
    wcel
    @36
    @38
    @40
    @52
    @72
    simprl3
    @47
    @49
    @51
    @41
    @72
    simprr3
    vj
    vk
    @39
    @50
    cA
    ctx
    txlly.1
    caovcl
    syl2anc
    eqeltrd
    @8
    @76
    vz
    @74
    @14
    @6
    @74
    wceq
    @7
    @75
    cA
    @6
    @74
    @4
    crest
    oveq2
    eleq1d
    rspcev
    syl2anc
    ex
    anassrs
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    mp2and
    expr
    rexlimdvva
    ralimdv
    sylbid
    ralrimiv
    vx
    vy
    vz
    cA
    @4
    isnlly
    sylanbrc
end
