include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "wrex.mm"
include "cutop.mm"
include "utopval.mm"
include "syl5eq.mm"
include "wb.mm"
include "simpll.mm"
include "simpr.mm"
include "elpwid.mm"
include "sselda.mm"
include "cvv.mm"
include "mptexg.mm"
include "rnexg.mm"
include "syl.mm"
include "adantr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "simplr.mm"
include "eqimss2.mm"
include "adantl.mm"
include "weq.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "r19.29af.mm"
include "ad2antrr.mm"
include "jca.mm"
include "ad3antrrr.mm"
include "eqeq2d.mm"
include "mpan2.mm"
include "imaex.mm"
include "ustuqtoplem.mm"
include "mpbird.mm"
include "syl21anc.mm"
include "w3a.mm"
include "wi.mm"
include "sseq1.mm"
include "3anbi2d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "ustuqtop1.mm"
include "vtocl.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "r19.29an.mm"
include "impbida.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "rabbidva.mm"
include "eqtr4d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "ustuqtop0.mm"
include "ustuqtop2.mm"
include "ustuqtop3.mm"
include "ustuqtop4.mm"
include "ustuqtop5.mm"
include "neiptopnei.mm"
include "sneqd.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "a1i.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel1.mm"
include "simpr2.mm"
include "imaeq2d.mm"
include "3anassrs.mm"
include "mpteq2da.mm"
include "rneqd.mm"
include "simpl.mm"
include "3eqtr2d.mm"

theorem utopsnneiplem
  let vv: setvar v
  let cP: class P
  let cU: class U
  let cJ: class J
  let cK: class K
  let cN: class N
  let cX: class X
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vu: setvar u
  let vw: setvar w
  assume utoptop.1: |- J = ( unifTop ` U )
  assume utopsnneip.1: |- K = { a e. ~P X | A. p e. a a e. ( N ` p ) }
  assume utopsnneip.2: |- N = ( p e. X |-> ran ( v e. U |-> ( v " { p } ) ) )

  disjoint a p
  disjoint K a
  disjoint K p
  disjoint N a
  disjoint N p
  disjoint p v
  disjoint P p
  disjoint P v
  disjoint a v
  disjoint U a
  disjoint U p
  disjoint U v
  disjoint X a
  disjoint X p
  disjoint X v
  disjoint a b
  disjoint a q
  disjoint b p
  disjoint b q
  disjoint N b
  disjoint p q
  disjoint N q
  disjoint a u
  disjoint a w
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint U b
  disjoint p u
  disjoint p w
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint U q
  disjoint u v
  disjoint u w
  disjoint U u
  disjoint v w
  disjoint U w
  disjoint X b
  disjoint X q
  disjoint X w
  assert |- ( ( U e. ( UnifOn ` X ) /\ P e. X ) -> ( ( nei ` J ) ` { P } ) = ran ( v e. U |-> ( v " { P } ) ) )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cP
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    @4
    cK
    cnei
    cfv
    #
    cfv
    #
    cP
    cN
    cfv
    #
    vv
    cU
    vv
    cv
    #
    @4
    cima
    #
    cmpt
    #
    crn
    #
    @1
    @6
    @8
    wceq
    @2
    @1
    @4
    @5
    @7
    @1
    cJ
    cK
    cnei
    @1
    cJ
    va
    cv
    #
    vp
    cv
    #
    cN
    cfv
    #
    wcel
    #
    vp
    @14
    wral
    #
    va
    cX
    cpw
    #
    crab
    #
    cK
    @1
    cJ
    vw
    cv
    #
    @15
    csn
    #
    cima
    #
    @14
    wss
    #
    vw
    cU
    wrex
    #
    vp
    @14
    wral
    #
    va
    @19
    crab
    #
    @20
    @1
    cJ
    cU
    cutop
    cfv
    @27
    utoptop.1
    vp
    vw
    cU
    cX
    va
    utopval
    syl5eq
    @1
    @18
    @26
    va
    @19
    @1
    @14
    @19
    wcel
    #
    wa
    #
    @17
    @25
    vp
    @14
    @29
    @15
    @14
    wcel
    #
    wa
    #
    @17
    @14
    @10
    @22
    cima
    #
    wceq
    #
    vv
    cU
    wrex
    #
    @25
    @31
    @1
    @15
    cX
    wcel
    #
    @17
    @34
    wb
    #
    @1
    @28
    @30
    simpll
    #
    @29
    @14
    cX
    @15
    @29
    @14
    cX
    @1
    @28
    simpr
    elpwid
    #
    sselda
    #
    @1
    @35
    wa
    #
    @17
    @14
    vv
    cU
    @32
    cmpt
    #
    crn
    #
    wcel
    #
    @34
    @40
    @16
    @42
    @14
    @40
    @35
    @42
    cvv
    wcel
    #
    @16
    @42
    wceq
    @1
    @35
    simpr
    @1
    @44
    @35
    @1
    @41
    cvv
    wcel
    @44
    vv
    cU
    @32
    @0
    mptexg
    @41
    cvv
    rnexg
    syl
    adantr
    vp
    cX
    @42
    cvv
    cN
    utopsnneip.2
    fvmpt2
    syl2anc
    eleq2d
    @14
    cvv
    wcel
    @43
    @34
    wb
    va
    vex
    vv
    cU
    @32
    @14
    @41
    cvv
    @41
    eqid
    elrnmpt
    ax-mp
    syl6bb
    #
    syl2anc
    @31
    @34
    @25
    @31
    @34
    wa
    #
    @33
    @25
    vv
    cU
    @31
    @34
    vv
    @31
    vv
    nfv
    @33
    vv
    cU
    nfre1
    nfan
    @46
    @10
    cU
    wcel
    #
    wa
    #
    @33
    wa
    @47
    @32
    @14
    wss
    #
    @25
    @46
    @47
    @33
    simplr
    @33
    @49
    @48
    @32
    @14
    eqimss2
    adantl
    @24
    @49
    vw
    @10
    cU
    vw
    vv
    weq
    @23
    @32
    @14
    @21
    @10
    @22
    imaeq1
    sseq1d
    rspcev
    syl2anc
    @31
    @34
    simpr
    r19.29af
    @31
    @24
    @34
    vw
    cU
    @31
    @21
    cU
    wcel
    #
    wa
    #
    @24
    wa
    #
    @17
    @34
    @52
    @40
    @24
    @14
    cX
    wss
    #
    @23
    @16
    wcel
    #
    @17
    @52
    @1
    @35
    @31
    @1
    @50
    @24
    @37
    ad2antrr
    #
    @31
    @35
    @50
    @24
    @39
    ad2antrr
    #
    jca
    #
    @51
    @24
    simpr
    @29
    @53
    @30
    @50
    @24
    @38
    ad3antrrr
    @52
    @1
    @35
    @50
    @54
    @55
    @56
    @31
    @50
    @24
    simplr
    @40
    @50
    wa
    @54
    @23
    vu
    cv
    #
    @22
    cima
    #
    wceq
    #
    vu
    cU
    wrex
    #
    @50
    @61
    @40
    @50
    @23
    @23
    wceq
    #
    @61
    @23
    eqid
    @60
    @62
    vu
    @21
    cU
    vu
    vw
    weq
    @59
    @23
    @23
    @58
    @21
    @22
    imaeq1
    eqeq2d
    rspcev
    mpan2
    adantl
    @40
    @54
    @61
    wb
    #
    @50
    @40
    @23
    cvv
    wcel
    @63
    @21
    @22
    vw
    vex
    imaex
    #
    vu
    vv
    @23
    @15
    cU
    cN
    cvv
    cX
    vp
    utopsnneip.2
    ustuqtoplem
    mpan2
    adantr
    mpbird
    syl21anc
    @40
    vb
    cv
    #
    @14
    wss
    #
    @53
    w3a
    #
    @65
    @16
    wcel
    #
    wa
    #
    @17
    wi
    @40
    @24
    @53
    w3a
    #
    @54
    wa
    #
    @17
    wi
    vb
    @23
    @64
    @65
    @23
    wceq
    #
    @69
    @71
    @17
    @72
    @67
    @70
    @68
    @54
    @72
    @66
    @24
    @40
    @53
    @65
    @23
    @14
    sseq1
    3anbi2d
    @65
    @23
    @16
    eleq1
    anbi12d
    imbi1d
    vv
    cU
    cN
    cX
    vp
    vb
    va
    utopsnneip.2
    ustuqtop1
    vtocl
    syl31anc
    @52
    @40
    @36
    @57
    @45
    syl
    mpbid
    r19.29an
    impbida
    bitrd
    ralbidva
    rabbidva
    eqtr4d
    utopsnneip.1
    syl6eqr
    fveq2d
    fveq1d
    adantr
    @3
    vp
    cP
    @22
    @7
    cfv
    #
    @8
    cX
    cN
    cvv
    @1
    cN
    vp
    cX
    @73
    cmpt
    wceq
    @2
    @1
    cK
    cN
    cX
    vq
    vp
    va
    vb
    utopsnneip.1
    vv
    cU
    cN
    cX
    vp
    utopsnneip.2
    ustuqtop0
    vv
    cU
    cN
    cX
    vp
    va
    vb
    utopsnneip.2
    ustuqtop1
    vv
    cU
    cN
    cX
    vp
    utopsnneip.2
    ustuqtop2
    vv
    cU
    cN
    cX
    vp
    va
    utopsnneip.2
    ustuqtop3
    vv
    cU
    cN
    cX
    vq
    vp
    va
    vb
    utopsnneip.2
    ustuqtop4
    vv
    cU
    cN
    cX
    vp
    utopsnneip.2
    ustuqtop5
    neiptopnei
    adantr
    @3
    @15
    cP
    wceq
    #
    wa
    #
    @22
    @4
    @7
    @75
    @15
    cP
    @3
    @74
    simpr
    sneqd
    fveq2d
    @1
    @2
    simpr
    #
    @3
    @4
    @7
    fvexd
    fvmptd
    @3
    @2
    @13
    cvv
    wcel
    #
    @9
    @13
    wceq
    @76
    @1
    @77
    @2
    @1
    @12
    cvv
    wcel
    @77
    vv
    cU
    @11
    @0
    mptexg
    @12
    cvv
    rnexg
    syl
    adantr
    @2
    @77
    wa
    #
    vp
    cP
    @42
    @13
    cX
    cN
    cvv
    cN
    vp
    cX
    @42
    cmpt
    wceq
    @78
    utopsnneip.2
    a1i
    @78
    @74
    wa
    #
    @41
    @12
    @79
    vv
    cU
    @32
    @11
    @78
    @74
    vv
    @2
    @77
    vv
    @2
    vv
    nfv
    vv
    @13
    cvv
    vv
    @12
    vv
    cU
    @11
    nfmpt1
    nfrn
    nfel1
    nfan
    @74
    vv
    nfv
    nfan
    @2
    @77
    @74
    @47
    @32
    @11
    wceq
    @2
    @77
    @74
    @47
    w3a
    wa
    #
    @22
    @4
    @10
    @80
    @15
    cP
    @2
    @77
    @74
    @47
    simpr2
    sneqd
    imaeq2d
    3anassrs
    mpteq2da
    rneqd
    @2
    @77
    simpl
    @2
    @77
    simpr
    fvmptd
    syl2anc
    3eqtr2d
end
