include "crngo.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cidl.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "wo.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cuni.mm"
include "c1st.mm"
include "crn.mm"
include "cgi.mm"
include "co.mm"
include "c2nd.mm"
include "dfss3.mm"
include "eqid.mm"
include "idlss.mm"
include "ex.mm"
include "ralimdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "unissb.mm"
include "sylibr.mm"
include "3ad2antr2.mm"
include "wrex.mm"
include "idl0cl.mm"
include "r19.2z.mm"
include "sylan2.mm"
include "an12s.mm"
include "eluni2.mm"
include "3adantr3.mm"
include "wel.mm"
include "wi.mm"
include "weq.mm"
include "sseq1.mm"
include "sseq2.mm"
include "orbi12d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "ad2antrl.mm"
include "ssel2.mm"
include "ancoms.mm"
include "adantll.mm"
include "idladdcl.mm"
include "ancom2s.mm"
include "expr.mm"
include "an32s.mm"
include "an42s.mm"
include "anasss.mm"
include "simprl.mm"
include "elunii.mm"
include "syl2anc.mm"
include "anassrs.mm"
include "ad2antrr.mm"
include "jaodan.mm"
include "syldan.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "3adantr1.mm"
include "idllmulcl.mm"
include "exp43.mm"
include "com23.mm"
include "imp41.mm"
include "sylanl2.mm"
include "simplrr.mm"
include "idlrmulcl.mm"
include "jca.mm"
include "ralrimiva.mm"
include "wb.mm"
include "isidl.mm"
include "mpbir3and.mm"

theorem unichnidl
  let cC: class C
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint R i
  disjoint C i
  disjoint C j
  disjoint i j
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  assert |- ( ( R e. RingOps /\ ( C =/= (/) /\ C C_ ( Idl ` R ) /\ A. i e. C A. j e. C ( i C_ j \/ j C_ i ) ) ) -> U. C e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cC
    c0
    wne
    #
    cC
    cR
    cidl
    cfv
    #
    wss
    #
    vi
    cv
    #
    vj
    cv
    #
    wss
    #
    @5
    @4
    wss
    #
    wo
    #
    vj
    cC
    wral
    #
    vi
    cC
    wral
    #
    w3a
    #
    wa
    #
    cC
    cuni
    #
    @2
    wcel
    #
    @13
    cR
    c1st
    cfv
    #
    crn
    #
    wss
    #
    @15
    cgi
    cfv
    #
    @13
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    @15
    co
    #
    @13
    wcel
    #
    vy
    @13
    wral
    #
    vz
    cv
    #
    @20
    cR
    c2nd
    cfv
    #
    co
    #
    @13
    wcel
    #
    @20
    @25
    @26
    co
    #
    @13
    wcel
    #
    wa
    #
    vz
    @16
    wral
    #
    wa
    #
    vx
    @13
    wral
    #
    @0
    @1
    @3
    @17
    @10
    @0
    @3
    wa
    #
    @4
    @16
    wss
    #
    vi
    cC
    wral
    #
    @17
    @3
    @0
    @4
    @2
    wcel
    #
    vi
    cC
    wral
    #
    @37
    vi
    cC
    @2
    dfss3
    #
    @0
    @39
    @37
    @0
    @38
    @36
    vi
    cC
    @0
    @38
    @36
    cR
    @15
    @4
    @16
    @15
    eqid
    #
    @16
    eqid
    #
    idlss
    ex
    ralimdv
    imp
    sylan2b
    vi
    cC
    @16
    unissb
    sylibr
    3ad2antr2
    @0
    @1
    @3
    @19
    @10
    @0
    @1
    @3
    wa
    wa
    @18
    @4
    wcel
    #
    vi
    cC
    wrex
    #
    @19
    @1
    @0
    @3
    @44
    @35
    @1
    @43
    vi
    cC
    wral
    #
    @44
    @3
    @0
    @39
    @45
    @40
    @0
    @39
    @45
    @0
    @38
    @43
    vi
    cC
    @0
    @38
    @43
    cR
    @15
    @4
    @18
    @41
    @18
    eqid
    #
    idl0cl
    ex
    ralimdv
    imp
    sylan2b
    @43
    vi
    cC
    r19.2z
    sylan2
    an12s
    vi
    @18
    cC
    eluni2
    sylibr
    3adantr3
    @12
    @33
    vx
    @13
    @20
    @13
    wcel
    vx
    vk
    wel
    #
    vk
    cC
    wrex
    @12
    @33
    vk
    @20
    cC
    eluni2
    @12
    @47
    @33
    vk
    cC
    @12
    vk
    cv
    #
    cC
    wcel
    #
    @47
    wa
    #
    wa
    @24
    @32
    @0
    @50
    @11
    @24
    @0
    @50
    wa
    #
    @3
    @10
    @24
    @1
    @51
    @3
    @10
    @24
    @51
    @3
    wa
    #
    @10
    @48
    @5
    wss
    #
    @5
    @48
    wss
    #
    wo
    #
    vj
    cC
    wral
    #
    @24
    @52
    @10
    @56
    @50
    @10
    @56
    wi
    #
    @0
    @3
    @49
    @57
    @47
    @9
    @56
    vi
    @48
    cC
    vi
    vk
    weq
    #
    @8
    @55
    vj
    cC
    @58
    @6
    @53
    @7
    @54
    @4
    @48
    @5
    sseq1
    @4
    @48
    @5
    sseq2
    orbi12d
    ralbidv
    rspcv
    adantr
    ad2antlr
    imp
    @52
    @56
    wa
    #
    @23
    vy
    @13
    @21
    @13
    wcel
    vy
    vi
    wel
    #
    vi
    cC
    wrex
    @59
    @23
    vi
    @21
    cC
    eluni2
    @59
    @60
    @23
    vi
    cC
    @52
    @4
    cC
    wcel
    #
    @60
    wa
    #
    @56
    @23
    @52
    @62
    wa
    #
    @56
    @48
    @4
    wss
    #
    @4
    @48
    wss
    #
    wo
    #
    @23
    @63
    @56
    @66
    @61
    @56
    @66
    wi
    @52
    @60
    @55
    @66
    vj
    @4
    cC
    vj
    vi
    weq
    @53
    @64
    @54
    @65
    @5
    @4
    @48
    sseq2
    @5
    @4
    @48
    sseq1
    orbi12d
    rspcv
    ad2antrl
    imp
    @63
    @64
    @23
    @65
    @63
    @64
    @23
    @51
    @3
    @62
    @64
    @23
    wi
    #
    @0
    @3
    @62
    wa
    #
    @50
    @67
    @0
    @68
    wa
    #
    @50
    @64
    @23
    @50
    @64
    wa
    @69
    vx
    vi
    wel
    #
    @23
    @47
    @64
    @70
    @49
    @64
    @47
    @70
    @48
    @4
    @20
    ssel2
    ancoms
    adantll
    @69
    @70
    wa
    @22
    @4
    wcel
    #
    @61
    @23
    @69
    @70
    @71
    @0
    @3
    @62
    @70
    @71
    wi
    #
    @0
    @60
    @3
    @61
    @72
    @3
    @61
    wa
    @0
    @60
    wa
    @38
    @72
    cC
    @2
    @4
    ssel2
    @0
    @38
    @60
    @72
    @0
    @38
    wa
    #
    @60
    @70
    @71
    @73
    @70
    @60
    @71
    @20
    @21
    cR
    @15
    @4
    @41
    idladdcl
    ancom2s
    expr
    an32s
    sylan2
    an42s
    anasss
    imp
    @68
    @61
    @0
    @70
    @3
    @61
    @60
    simprl
    ad2antlr
    @22
    @4
    cC
    elunii
    syl2anc
    sylan2
    expr
    an32s
    anassrs
    imp
    @52
    @62
    @65
    @23
    @62
    @65
    wa
    @52
    vy
    vk
    wel
    #
    @23
    @60
    @65
    @74
    @61
    @65
    @60
    @74
    @4
    @48
    @21
    ssel2
    ancoms
    adantll
    @52
    @74
    wa
    @22
    @48
    wcel
    #
    @49
    @23
    @52
    @74
    @75
    @0
    @3
    @50
    @74
    @75
    wi
    #
    @0
    @47
    @3
    @49
    @76
    @3
    @49
    wa
    #
    @0
    @47
    wa
    #
    @48
    @2
    wcel
    #
    @76
    cC
    @2
    @48
    ssel2
    #
    @0
    @79
    @47
    @76
    @0
    @79
    wa
    @47
    @74
    @75
    @20
    @21
    cR
    @15
    @48
    @41
    idladdcl
    expr
    an32s
    sylan2
    an42s
    an32s
    imp
    @51
    @49
    @3
    @74
    @0
    @49
    @47
    simprl
    ad2antrr
    @22
    @48
    cC
    elunii
    syl2anc
    sylan2
    anassrs
    jaodan
    syldan
    an32s
    rexlimdvaa
    syl5bi
    ralrimiv
    syldan
    anasss
    3adantr1
    an32s
    @0
    @50
    @11
    @32
    @51
    @1
    @3
    @32
    @10
    @0
    @3
    @50
    @32
    @0
    @47
    @3
    @49
    @32
    @78
    @77
    wa
    #
    @31
    vz
    @16
    @81
    @25
    @16
    wcel
    #
    wa
    #
    @28
    @30
    @83
    @27
    @48
    wcel
    #
    @49
    @28
    @77
    @78
    @79
    @82
    @84
    @80
    @0
    @47
    @79
    @82
    @84
    @0
    @79
    @47
    @82
    @84
    wi
    @0
    @79
    @47
    @82
    @84
    @20
    @25
    cR
    @15
    @26
    @48
    @16
    @41
    @26
    eqid
    #
    @42
    idllmulcl
    exp43
    com23
    imp41
    sylanl2
    @78
    @3
    @49
    @82
    simplrr
    #
    @27
    @48
    cC
    elunii
    syl2anc
    @83
    @29
    @48
    wcel
    #
    @49
    @30
    @77
    @78
    @79
    @82
    @87
    @80
    @0
    @47
    @79
    @82
    @87
    @0
    @79
    @47
    @82
    @87
    wi
    @0
    @79
    @47
    @82
    @87
    @20
    @25
    cR
    @15
    @26
    @48
    @16
    @41
    @85
    @42
    idlrmulcl
    exp43
    com23
    imp41
    sylanl2
    @86
    @29
    @48
    cC
    elunii
    syl2anc
    jca
    ralrimiva
    an42s
    an32s
    3ad2antr2
    an32s
    jca
    rexlimdvaa
    syl5bi
    ralrimiv
    @0
    @14
    @17
    @19
    @34
    w3a
    wb
    @11
    vx
    vy
    vz
    cR
    @15
    @26
    @13
    @16
    @18
    @41
    @85
    @42
    @46
    isidl
    adantr
    mpbir3and
end
