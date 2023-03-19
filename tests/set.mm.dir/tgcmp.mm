include "ctb.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "ctg.mm"
include "cfv.mm"
include "ccmp.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "eqid.mm"
include "iscmp.mm"
include "simprbi.mm"
include "unitg.mm"
include "eqtr3.mm"
include "sylan.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "wss.mm"
include "bastg.mm"
include "adantr.mm"
include "sspwb.mm"
include "sylib.mm"
include "ssralv.mm"
include "syl.mm"
include "sylbid.mm"
include "syl5.mm"
include "elpwi.mm"
include "crab.mm"
include "simprr.mm"
include "wel.mm"
include "simprl.mm"
include "sselda.mm"
include "adantrr.mm"
include "tg2.mm"
include "syl2anc.mm"
include "expr.mm"
include "reximdva.mm"
include "eluni2.mm"
include "elunirab.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "rexcom.mm"
include "3bitr2i.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "eqsstrd.mm"
include "ssrab2.mm"
include "unissi.mm"
include "simplr.mm"
include "syl5sseqr.mm"
include "eqssd.mm"
include "wb.mm"
include "elpw2g.mm"
include "ad2antrr.mm"
include "mpbiri.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "rspcv.mm"
include "mpid.mm"
include "wf.mm"
include "wex.mm"
include "elfpw.mm"
include "ad2antrl.mm"
include "simplbi.mm"
include "ssrab.mm"
include "sseq2.mm"
include "ac6sfi.mm"
include "crn.mm"
include "frn.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "syl2an.mm"
include "sylanbrc.mm"
include "simplrr.mm"
include "ciun.mm"
include "uniiun.mm"
include "ss2iun.mm"
include "syl5eqss.mm"
include "ad2antll.mm"
include "fniunfv.mm"
include "sseqtrd.mm"
include "unissd.mm"
include "sseqtr4d.mm"
include "rspcev.mm"
include "exlimddv.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "com23.mm"
include "sylan2.mm"
include "ralrimdva.mm"
include "tgcl.mm"
include "baib.mm"
include "bitrd.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem tgcmp
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cX: class X
  let vf: setvar f
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w

  disjoint y z
  disjoint B y
  disjoint B z
  disjoint X y
  disjoint X z
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint X f
  disjoint X t
  disjoint X u
  disjoint X v
  assert |- ( ( B e. TopBases /\ X = U. B ) -> ( ( topGen ` B ) e. Comp <-> A. y e. ~P B ( X = U. y -> E. z e. ( ~P y i^i Fin ) X = U. z ) ) )

  proof
    cB
    ctb
    wcel
    #
    cX
    cB
    cuni
    #
    wceq
    #
    wa
    #
    cB
    ctg
    cfv
    #
    ccmp
    wcel
    #
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    @6
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    cB
    cpw
    #
    wral
    #
    @5
    @4
    cuni
    #
    @7
    wceq
    #
    @18
    @10
    wceq
    #
    vz
    @13
    wrex
    #
    wi
    #
    vy
    @4
    cpw
    #
    wral
    #
    @3
    @17
    @5
    @4
    ctop
    wcel
    #
    @24
    vy
    vz
    @4
    @18
    @18
    eqid
    #
    iscmp
    simprbi
    @3
    @24
    @15
    vy
    @23
    wral
    #
    @17
    @3
    @22
    @15
    vy
    @23
    @3
    @19
    @8
    @21
    @14
    @3
    @18
    cX
    @7
    @0
    @18
    @1
    wceq
    @2
    @18
    cX
    wceq
    cB
    ctb
    unitg
    @18
    cX
    @1
    eqtr3
    sylan
    #
    eqeq1d
    @3
    @20
    @11
    vz
    @13
    @3
    @18
    cX
    @10
    @28
    eqeq1d
    rexbidv
    imbi12d
    ralbidv
    @3
    @16
    @23
    wss
    #
    @27
    @17
    wi
    @3
    cB
    @4
    wss
    #
    @29
    @0
    @30
    @2
    cB
    ctb
    bastg
    adantr
    cB
    @4
    sspwb
    sylib
    @15
    vy
    @16
    @23
    ssralv
    syl
    sylbid
    syl5
    @3
    @17
    cX
    vu
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vv
    cv
    #
    cuni
    #
    wceq
    #
    vv
    @31
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vu
    @23
    wral
    #
    @5
    @3
    @17
    @39
    vu
    @23
    @31
    @23
    wcel
    @3
    @31
    @4
    wss
    #
    @17
    @39
    wi
    @31
    @4
    elpwi
    @3
    @41
    wa
    @33
    @17
    @38
    @3
    @41
    @33
    @17
    @38
    wi
    @3
    @41
    @33
    wa
    #
    wa
    #
    @17
    @11
    vz
    vw
    cv
    #
    vt
    cv
    #
    wss
    #
    vt
    @31
    wrex
    #
    vw
    cB
    crab
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @38
    @43
    @17
    cX
    @48
    cuni
    #
    wceq
    #
    @51
    @43
    cX
    @52
    @43
    cX
    @32
    @52
    @3
    @41
    @33
    simprr
    #
    @43
    vy
    @32
    @52
    @43
    vy
    vt
    wel
    #
    vt
    @31
    wrex
    vy
    vw
    wel
    #
    @46
    wa
    #
    vw
    cB
    wrex
    #
    vt
    @31
    wrex
    #
    @6
    @32
    wcel
    @6
    @52
    wcel
    #
    @43
    @55
    @58
    vt
    @31
    @43
    vt
    vu
    wel
    #
    @55
    @58
    @43
    @61
    @55
    wa
    wa
    @45
    @4
    wcel
    #
    @55
    @58
    @43
    @61
    @62
    @55
    @43
    @31
    @4
    @45
    @3
    @41
    @33
    simprl
    sselda
    adantrr
    @43
    @61
    @55
    simprr
    vw
    @45
    cB
    @6
    tg2
    syl2anc
    expr
    reximdva
    vt
    @6
    @31
    eluni2
    @60
    @56
    @47
    wa
    #
    vw
    cB
    wrex
    @57
    vt
    @31
    wrex
    #
    vw
    cB
    wrex
    @59
    @47
    vw
    @6
    cB
    elunirab
    @64
    @63
    vw
    cB
    @56
    @46
    vt
    @31
    r19.42v
    rexbii
    @57
    vw
    vt
    cB
    @31
    rexcom
    3bitr2i
    3imtr4g
    ssrdv
    eqsstrd
    @43
    @1
    @52
    cX
    @48
    cB
    @47
    vw
    cB
    ssrab2
    #
    unissi
    @0
    @2
    @42
    simplr
    syl5sseqr
    eqssd
    @43
    @48
    @16
    wcel
    #
    @17
    @53
    @51
    wi
    #
    wi
    @43
    @66
    @48
    cB
    wss
    #
    @65
    @0
    @66
    @68
    wb
    @2
    @42
    @48
    cB
    ctb
    elpw2g
    ad2antrr
    mpbiri
    @15
    @67
    vy
    @48
    @16
    @6
    @48
    wceq
    #
    @8
    @53
    @14
    @51
    @69
    @7
    @52
    cX
    @6
    @48
    unieq
    eqeq2d
    @69
    @11
    vz
    @13
    @50
    @69
    @12
    @49
    cfn
    @6
    @48
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcv
    syl
    mpid
    @43
    @11
    @38
    vz
    @50
    @43
    @9
    @50
    wcel
    #
    @11
    wa
    #
    wa
    #
    @9
    @31
    vf
    cv
    #
    wf
    #
    @44
    @44
    @73
    cfv
    #
    wss
    #
    vw
    @9
    wral
    #
    wa
    #
    @38
    vf
    @72
    @9
    cfn
    wcel
    #
    @47
    vw
    @9
    wral
    #
    @78
    vf
    wex
    @70
    @79
    @43
    @11
    @70
    @9
    @48
    wss
    #
    @79
    @9
    @48
    elfpw
    #
    simprbi
    ad2antrl
    #
    @72
    @81
    @80
    @70
    @81
    @43
    @11
    @70
    @81
    @79
    @82
    simplbi
    ad2antrl
    @81
    @9
    cB
    wss
    @80
    @47
    vw
    cB
    @9
    ssrab
    simprbi
    syl
    @46
    @76
    vw
    vt
    @9
    @31
    vf
    @45
    @75
    @44
    sseq2
    ac6sfi
    syl2anc
    @72
    @78
    wa
    #
    @73
    crn
    #
    @37
    wcel
    #
    cX
    @85
    cuni
    #
    wceq
    #
    @38
    @84
    @85
    @31
    wss
    #
    @85
    cfn
    wcel
    #
    @86
    @74
    @89
    @72
    @77
    @9
    @31
    @73
    frn
    ad2antrl
    #
    @72
    @79
    @9
    @85
    @73
    wfo
    #
    @90
    @78
    @83
    @74
    @92
    @77
    @74
    @73
    @9
    wfn
    #
    @92
    @9
    @31
    @73
    ffn
    #
    @9
    @73
    dffn4
    sylib
    adantr
    @9
    @85
    @73
    fofi
    syl2an
    @85
    @31
    elfpw
    sylanbrc
    @84
    cX
    @87
    @84
    cX
    @10
    @87
    @43
    @70
    @11
    @78
    simplrr
    @84
    @10
    vw
    @9
    @75
    ciun
    #
    @87
    @77
    @10
    @95
    wss
    @72
    @74
    @77
    @10
    vw
    @9
    @44
    ciun
    @95
    vw
    @9
    uniiun
    vw
    @9
    @44
    @75
    ss2iun
    syl5eqss
    ad2antll
    @74
    @95
    @87
    wceq
    #
    @72
    @77
    @74
    @93
    @96
    @94
    vw
    @9
    @73
    fniunfv
    syl
    ad2antrl
    sseqtrd
    eqsstrd
    @84
    @87
    @32
    cX
    @84
    @85
    @31
    @91
    unissd
    @43
    @33
    @71
    @78
    @54
    ad2antrr
    sseqtr4d
    eqssd
    @36
    @88
    vv
    @85
    @37
    @34
    @85
    wceq
    @35
    @87
    cX
    @34
    @85
    unieq
    eqeq2d
    rspcev
    syl2anc
    exlimddv
    rexlimdvaa
    syld
    expr
    com23
    sylan2
    ralrimdva
    @3
    @5
    @18
    @32
    wceq
    #
    @18
    @35
    wceq
    #
    vv
    @37
    wrex
    #
    wi
    #
    vu
    @23
    wral
    #
    @40
    @3
    @25
    @5
    @101
    wb
    @0
    @25
    @2
    cB
    tgcl
    adantr
    @5
    @25
    @101
    vu
    vv
    @4
    @18
    @26
    iscmp
    baib
    syl
    @3
    @100
    @39
    vu
    @23
    @3
    @97
    @33
    @99
    @38
    @3
    @18
    cX
    @32
    @28
    eqeq1d
    @3
    @98
    @36
    vv
    @37
    @3
    @18
    cX
    @35
    @28
    eqeq1d
    rexbidv
    imbi12d
    ralbidv
    bitrd
    sylibrd
    impbid
end
