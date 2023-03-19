include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "cgic.mm"
include "wbr.mm"
include "cghm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cplusg.mm"
include "eqid.mm"
include "cn0.mm"
include "ccrg.mm"
include "crg.mm"
include "cgrp.mm"
include "cfn.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "hashcl.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "0nn0.mm"
include "a1i.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "zncrng.mm"
include "crngring.mm"
include "ringgrp.mm"
include "4syl.mm"
include "ccyg.mm"
include "cyggrp.mm"
include "syl.mm"
include "cygznlem2a.mm"
include "cv.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "wfo.mm"
include "znzrhfo.mm"
include "foelrn.mm"
include "sylan.mm"
include "anim12dan.mm"
include "reeanv.mm"
include "caddc.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "cmpt.mm"
include "crn.mm"
include "iscyggen.mm"
include "simplbi.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "zring.mm"
include "crh.mm"
include "zrhrhm.mm"
include "rhmghm.mm"
include "zringbas.mm"
include "zringplusg.mm"
include "ghmlin.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "zaddcl.mm"
include "cygznlem2.mm"
include "sylan2.mm"
include "eqtr3d.mm"
include "adantrr.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "oveq12.mm"
include "fveq2.mm"
include "oveqan12d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "imp.mm"
include "syldan.mm"
include "isghmd.mm"
include "wf1.mm"
include "wf.mm"
include "wi.mm"
include "wral.mm"
include "cygznlem1.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "eqeqan12d.mm"
include "eqeq12.mm"
include "imbi12d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "wb.mm"
include "iscyggen2.mm"
include "mpbid.mm"
include "simprd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "fof.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "eqcomd.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralimdva.mm"
include "mpd.mm"
include "dffo3.mm"
include "df-f1o.mm"
include "isgim.mm"
include "brgici.mm"
include "gicsym.mm"
include "3syl.mm"

theorem cygznlem3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  let cM: class M
  assume cygzn.b: |- B = ( Base ` G )
  assume cygzn.n: |- N = if ( B e. Fin , ( # ` B ) , 0 )
  assume cygzn.y: |- Y = ( Z/nZ ` N )
  assume cygzn.m: |- .x. = ( .g ` G )
  assume cygzn.l: |- L = ( ZRHom ` Y )
  assume cygzn.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }
  assume cygzn.g: |- ( ph -> G e. CycGrp )
  assume cygzn.x: |- ( ph -> X e. E )
  assume cygzn.f: |- F = ran ( m e. ZZ |-> <. ( L ` m ) , ( m .x. X ) >. )

  disjoint m n
  disjoint m x
  disjoint B m
  disjoint n x
  disjoint B n
  disjoint B x
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint L m
  disjoint L n
  disjoint L x
  disjoint N x
  disjoint m ph
  disjoint F n
  disjoint F x
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint a b
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a z
  disjoint B a
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b z
  disjoint B b
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g z
  disjoint B g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i z
  disjoint B i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j z
  disjoint B j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint B k
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint B z
  disjoint E z
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G z
  disjoint M m
  disjoint .x. a
  disjoint .x. j
  disjoint .x. k
  disjoint .x. z
  disjoint Y a
  disjoint Y b
  disjoint Y g
  disjoint Y i
  disjoint Y j
  disjoint Y z
  disjoint L a
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint F a
  disjoint F b
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F z
  disjoint X a
  disjoint X j
  disjoint X k
  disjoint X z
  assert |- ( ph -> G ~=g Y )

  proof
    wph
    cF
    cY
    cG
    cgim
    co
    wcel
    #
    cY
    cG
    cgic
    wbr
    cG
    cY
    cgic
    wbr
    wph
    cF
    cY
    cG
    cghm
    co
    wcel
    cY
    cbs
    cfv
    #
    cB
    cF
    wf1o
    #
    @0
    wph
    va
    vb
    cY
    cplusg
    cfv
    #
    cG
    cplusg
    cfv
    #
    cY
    cG
    cF
    @1
    cB
    @1
    eqid
    #
    cygzn.b
    @3
    eqid
    #
    @4
    eqid
    #
    wph
    cN
    cn0
    wcel
    #
    cY
    ccrg
    wcel
    #
    cY
    crg
    wcel
    #
    cY
    cgrp
    wcel
    wph
    cN
    cB
    cfn
    wcel
    #
    cB
    chash
    cfv
    #
    cc0
    cif
    cn0
    cygzn.n
    wph
    @11
    @12
    cc0
    cn0
    @11
    @12
    cn0
    wcel
    wph
    cB
    hashcl
    adantl
    cc0
    cn0
    wcel
    wph
    @11
    wn
    wa
    0nn0
    a1i
    ifclda
    syl5eqel
    #
    cN
    cY
    cygzn.y
    zncrng
    #
    cY
    crngring
    #
    cY
    ringgrp
    4syl
    wph
    cG
    ccyg
    wcel
    cG
    cgrp
    wcel
    #
    cygzn.g
    cG
    cyggrp
    syl
    #
    wph
    vx
    cB
    c.x
    vm
    vn
    cE
    cF
    cG
    cL
    cN
    cX
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    cygzn.m
    cygzn.l
    cygzn.e
    cygzn.g
    cygzn.x
    cygzn.f
    cygznlem2a
    #
    wph
    va
    cv
    #
    @1
    wcel
    #
    vb
    cv
    #
    @1
    wcel
    #
    wa
    #
    @19
    vi
    cv
    #
    cL
    cfv
    #
    wceq
    #
    vi
    cz
    wrex
    #
    @21
    vj
    cv
    #
    cL
    cfv
    #
    wceq
    #
    vj
    cz
    wrex
    #
    wa
    #
    @19
    @21
    @3
    co
    #
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    @21
    cF
    cfv
    #
    @4
    co
    #
    wceq
    #
    wph
    @20
    @27
    @22
    @31
    wph
    cz
    @1
    cL
    wfo
    #
    @20
    @27
    wph
    @8
    @39
    @13
    @1
    cL
    cN
    cY
    cygzn.y
    @5
    cygzn.l
    znzrhfo
    syl
    #
    vi
    cz
    @1
    @19
    cL
    foelrn
    sylan
    wph
    @39
    @22
    @31
    @40
    vj
    cz
    @1
    @21
    cL
    foelrn
    sylan
    anim12dan
    #
    wph
    @32
    @38
    @32
    @26
    @30
    wa
    #
    vj
    cz
    wrex
    vi
    cz
    wrex
    #
    wph
    @38
    @26
    @30
    vi
    vj
    cz
    cz
    reeanv
    #
    wph
    @42
    @38
    vi
    vj
    cz
    cz
    wph
    @24
    cz
    wcel
    #
    @28
    cz
    wcel
    #
    wa
    #
    wa
    #
    @38
    @42
    @25
    @29
    @3
    co
    #
    cF
    cfv
    #
    @25
    cF
    cfv
    #
    @29
    cF
    cfv
    #
    @4
    co
    #
    wceq
    @48
    @24
    @28
    caddc
    co
    #
    cX
    c.x
    co
    #
    @24
    cX
    c.x
    co
    #
    @28
    cX
    c.x
    co
    #
    @4
    co
    #
    @50
    @53
    @48
    @16
    @45
    @46
    cX
    cB
    wcel
    #
    @55
    @58
    wceq
    wph
    @16
    @47
    @17
    adantr
    wph
    @45
    @46
    simprl
    #
    wph
    @45
    @46
    simprr
    #
    wph
    @59
    @47
    wph
    cX
    cE
    wcel
    #
    @59
    cygzn.x
    @62
    @59
    vn
    cz
    vn
    cv
    #
    cX
    c.x
    co
    #
    cmpt
    crn
    cB
    wceq
    vx
    cB
    c.x
    vn
    cE
    cG
    cX
    cygzn.b
    cygzn.m
    cygzn.e
    iscyggen
    simplbi
    syl
    adantr
    cB
    @4
    c.x
    cG
    @24
    @28
    cX
    cygzn.b
    cygzn.m
    @7
    mulgdir
    syl13anc
    @48
    @54
    cL
    cfv
    #
    cF
    cfv
    #
    @50
    @55
    @48
    @65
    @49
    cF
    @48
    cL
    zring
    cY
    cghm
    co
    wcel
    #
    @45
    @46
    @65
    @49
    wceq
    wph
    @67
    @47
    wph
    @9
    @10
    cL
    zring
    cY
    crh
    co
    wcel
    @67
    wph
    @8
    @9
    @13
    @14
    syl
    @15
    cY
    cL
    cygzn.l
    zrhrhm
    zring
    cY
    cL
    rhmghm
    4syl
    adantr
    @60
    @61
    caddc
    @3
    zring
    cY
    @24
    cL
    @28
    cz
    zringbas
    zringplusg
    @6
    ghmlin
    syl3anc
    fveq2d
    @47
    wph
    @54
    cz
    wcel
    @66
    @55
    wceq
    @24
    @28
    zaddcl
    wph
    vx
    cB
    c.x
    vm
    vn
    cE
    cF
    cG
    cL
    @54
    cN
    cX
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    cygzn.m
    cygzn.l
    cygzn.e
    cygzn.g
    cygzn.x
    cygzn.f
    cygznlem2
    sylan2
    eqtr3d
    @48
    @51
    @56
    @52
    @57
    @4
    wph
    @45
    @51
    @56
    wceq
    @46
    wph
    vx
    cB
    c.x
    vm
    vn
    cE
    cF
    cG
    cL
    @24
    cN
    cX
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    cygzn.m
    cygzn.l
    cygzn.e
    cygzn.g
    cygzn.x
    cygzn.f
    cygznlem2
    adantrr
    #
    wph
    @46
    @52
    @57
    wceq
    #
    @45
    wph
    vx
    cB
    c.x
    vm
    vn
    cE
    cF
    cG
    cL
    @28
    cN
    cX
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    cygzn.m
    cygzn.l
    cygzn.e
    cygzn.g
    cygzn.x
    cygzn.f
    cygznlem2
    #
    adantrl
    #
    oveq12d
    3eqtr4d
    @42
    @34
    @50
    @37
    @53
    @42
    @33
    @49
    cF
    @19
    @25
    @21
    @29
    @3
    oveq12
    fveq2d
    @26
    @30
    @35
    @51
    @36
    @52
    @4
    @19
    @25
    cF
    fveq2
    #
    @21
    @29
    cF
    fveq2
    #
    oveqan12d
    eqeq12d
    syl5ibrcom
    rexlimdvva
    syl5bir
    imp
    syldan
    isghmd
    wph
    @1
    cB
    cF
    wf1
    #
    @1
    cB
    cF
    wfo
    #
    @2
    wph
    @1
    cB
    cF
    wf
    #
    @35
    @36
    wceq
    #
    @19
    @21
    wceq
    #
    wi
    #
    vb
    @1
    wral
    va
    @1
    wral
    @74
    @18
    wph
    @79
    va
    vb
    @1
    @1
    wph
    @23
    @32
    @79
    @41
    wph
    @32
    @79
    @32
    @43
    wph
    @79
    @44
    wph
    @42
    @79
    vi
    vj
    cz
    cz
    @48
    @79
    @42
    @51
    @52
    wceq
    #
    @25
    @29
    wceq
    #
    wi
    @48
    @80
    @81
    @48
    @80
    @56
    @57
    wceq
    @81
    @48
    @51
    @56
    @52
    @57
    @68
    @71
    eqeq12d
    wph
    vx
    cB
    c.x
    vn
    cE
    cG
    @24
    cL
    @28
    cN
    cX
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    cygzn.m
    cygzn.l
    cygzn.e
    cygzn.g
    cygzn.x
    cygznlem1
    bitr4d
    biimpd
    @42
    @77
    @80
    @78
    @81
    @26
    @30
    @35
    @51
    @36
    @52
    @72
    @73
    eqeqan12d
    @19
    @25
    @21
    @29
    eqeq12
    imbi12d
    syl5ibrcom
    rexlimdvva
    syl5bir
    imp
    syldan
    ralrimivva
    va
    vb
    @1
    cB
    cF
    dff13
    sylanbrc
    wph
    @76
    vz
    cv
    #
    @35
    wceq
    #
    va
    @1
    wrex
    #
    vz
    cB
    wral
    #
    @75
    @18
    wph
    @82
    @64
    wceq
    #
    vn
    cz
    wrex
    #
    vz
    cB
    wral
    #
    @85
    wph
    @59
    @88
    wph
    @62
    @59
    @88
    wa
    #
    cygzn.x
    wph
    @16
    @62
    @89
    wb
    @17
    vx
    vz
    cB
    c.x
    vn
    cE
    cG
    cX
    cygzn.b
    cygzn.m
    cygzn.e
    iscyggen2
    syl
    mpbid
    simprd
    wph
    @87
    @84
    vz
    cB
    @87
    @82
    @57
    wceq
    #
    vj
    cz
    wrex
    wph
    @82
    cB
    wcel
    #
    wa
    #
    @84
    @86
    @90
    vn
    vj
    cz
    @63
    @28
    wceq
    @64
    @57
    @82
    @63
    @28
    cX
    c.x
    oveq1
    eqeq2d
    cbvrexv
    @92
    @90
    @84
    vj
    cz
    @92
    @46
    wa
    #
    @84
    @90
    @57
    @35
    wceq
    #
    va
    @1
    wrex
    #
    @93
    @29
    @1
    wcel
    @57
    @52
    wceq
    #
    @95
    @92
    cz
    @1
    @28
    cL
    @92
    @39
    cz
    @1
    cL
    wf
    wph
    @39
    @91
    @40
    adantr
    cz
    @1
    cL
    fof
    syl
    ffvelrnda
    @93
    @52
    @57
    wph
    @46
    @69
    @91
    @70
    adantlr
    eqcomd
    @94
    @96
    va
    @29
    @1
    @19
    @29
    wceq
    @35
    @52
    @57
    @19
    @29
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @90
    @83
    @94
    va
    @1
    @82
    @57
    @35
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    syl5bi
    ralimdva
    mpd
    va
    vz
    @1
    cB
    cF
    dffo3
    sylanbrc
    @1
    cB
    cF
    df-f1o
    sylanbrc
    @1
    cB
    cY
    cG
    cF
    @5
    cygzn.b
    isgim
    sylanbrc
    cY
    cG
    cF
    brgici
    cY
    cG
    gicsym
    3syl
end
