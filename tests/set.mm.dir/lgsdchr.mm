include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "cc.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cui.mm"
include "wral.mm"
include "cur.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "wi.mm"
include "w3a.mm"
include "wss.mm"
include "clgs.mm"
include "cz.mm"
include "wrex.mm"
include "cio.mm"
include "cvv.mm"
include "iotaex.mm"
include "a1i.mm"
include "cmpt.mm"
include "wfo.mm"
include "cn0.mm"
include "nnnn0.mm"
include "adantr.mm"
include "znzrhfo.mm"
include "syl.mm"
include "foelrn.mm"
include "sylan.mm"
include "lgsdchrval.mm"
include "simpr.mm"
include "nnz.mm"
include "ad2antrr.mm"
include "lgscl.mm"
include "syl2anc.mm"
include "zred.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "imp.mm"
include "syldan.mm"
include "fmpt2d.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "eqid.mm"
include "unitss.mm"
include "anim12dan.mm"
include "reeanv.mm"
include "adantrr.mm"
include "simprr.mm"
include "lgsdirnn0.mm"
include "syl3anc.mm"
include "zring.mm"
include "crh.mm"
include "crg.mm"
include "ccrg.mm"
include "zncrng.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "fveq2d.mm"
include "zmulcl.mm"
include "sylan2.mm"
include "eqtr3d.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "oveq12.mm"
include "oveqan12d.mm"
include "eqeq12d.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "ralrimivva.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "mpsyl.mm"
include "1z.mm"
include "mpan2.mm"
include "zrh1.mm"
include "1lgs.mm"
include "3eqtr3d.mm"
include "cgcd.mm"
include "wb.mm"
include "lgsne0.mm"
include "biimpd.mm"
include "neeq1d.mm"
include "znunit.mm"
include "3imtr4d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "simpl.mm"
include "dchrelbas3.mm"
include "mpbir2and.mm"
include "jca.mm"

theorem lgsdchr
  let vy: setvar y
  let cB: class B
  let cD: class D
  let vh: setvar h
  let vm: setvar m
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let cA: class A
  assume lgsdchr.g: |- G = ( DChr ` N )
  assume lgsdchr.z: |- Z = ( Z/nZ ` N )
  assume lgsdchr.d: |- D = ( Base ` G )
  assume lgsdchr.b: |- B = ( Base ` Z )
  assume lgsdchr.l: |- L = ( ZRHom ` Z )
  assume lgsdchr.x: |- X = ( y e. B |-> ( iota h E. m e. ZZ ( y = ( L ` m ) /\ h = ( m /L N ) ) ) )

  disjoint B y
  disjoint h m
  disjoint h y
  disjoint L h
  disjoint m y
  disjoint L m
  disjoint L y
  disjoint N h
  disjoint N m
  disjoint N y
  disjoint X y
  disjoint Z y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint x y
  disjoint B x
  disjoint a h
  disjoint a m
  disjoint L a
  disjoint b h
  disjoint b m
  disjoint L b
  disjoint N a
  disjoint N b
  disjoint h x
  disjoint m x
  disjoint N x
  disjoint X a
  disjoint X b
  disjoint X x
  disjoint A h
  disjoint A m
  disjoint A y
  disjoint Z a
  disjoint Z b
  disjoint Z x
  assert |- ( ( N e. NN /\ -. 2 || N ) -> ( X e. D /\ X : B --> RR ) )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    wa
    #
    cX
    cD
    wcel
    #
    cB
    cr
    cX
    wf
    #
    @2
    @3
    cB
    cc
    cX
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cZ
    cmulr
    cfv
    #
    co
    #
    cX
    cfv
    #
    @6
    cX
    cfv
    #
    @7
    cX
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cZ
    cui
    cfv
    #
    wral
    #
    vx
    @15
    wral
    #
    cZ
    cur
    cfv
    #
    cX
    cfv
    #
    c1
    wceq
    #
    @11
    cc0
    wne
    #
    @6
    @15
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    w3a
    @2
    @4
    cr
    cc
    wss
    @5
    @2
    vy
    vx
    cB
    @7
    vm
    cv
    #
    cL
    cfv
    wceq
    vh
    cv
    @25
    cN
    clgs
    co
    wceq
    wa
    vm
    cz
    wrex
    #
    vh
    cio
    #
    cr
    cX
    cvv
    @27
    cvv
    wcel
    @2
    @7
    cB
    wcel
    #
    wa
    @26
    vh
    iotaex
    a1i
    cX
    vy
    cB
    @27
    cmpt
    wceq
    @2
    lgsdchr.x
    a1i
    @2
    @6
    cB
    wcel
    #
    @6
    va
    cv
    #
    cL
    cfv
    #
    wceq
    #
    va
    cz
    wrex
    #
    @11
    cr
    wcel
    #
    @2
    cz
    cB
    cL
    wfo
    #
    @29
    @33
    @2
    cN
    cn0
    wcel
    #
    @35
    @0
    @36
    @1
    cN
    nnnn0
    adantr
    #
    cB
    cL
    cN
    cZ
    lgsdchr.z
    lgsdchr.b
    lgsdchr.l
    znzrhfo
    syl
    #
    va
    cz
    cB
    @6
    cL
    foelrn
    sylan
    #
    @2
    @33
    @34
    @2
    @32
    @34
    va
    cz
    @2
    @30
    cz
    wcel
    #
    wa
    #
    @34
    @32
    @31
    cX
    cfv
    #
    cr
    wcel
    @41
    @42
    @30
    cN
    clgs
    co
    #
    cr
    vy
    @30
    cB
    cD
    vh
    vm
    cG
    cL
    cN
    cX
    cZ
    lgsdchr.g
    lgsdchr.z
    lgsdchr.d
    lgsdchr.b
    lgsdchr.l
    lgsdchr.x
    lgsdchrval
    #
    @41
    @43
    @41
    @40
    cN
    cz
    wcel
    #
    @43
    cz
    wcel
    @2
    @40
    simpr
    #
    @0
    @45
    @1
    @40
    cN
    nnz
    #
    ad2antrr
    #
    @30
    cN
    lgscl
    syl2anc
    zred
    eqeltrd
    @32
    @11
    @42
    cr
    @6
    @31
    cX
    fveq2
    #
    eleq1d
    syl5ibrcom
    rexlimdva
    imp
    syldan
    fmpt2d
    #
    ax-resscn
    cB
    cr
    cc
    cX
    fss
    sylancl
    @2
    @17
    @20
    @24
    @15
    cB
    wss
    #
    @2
    @14
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @17
    cB
    cZ
    @15
    lgsdchr.b
    @15
    eqid
    #
    unitss
    @2
    @14
    vx
    vy
    cB
    cB
    @2
    @29
    @28
    wa
    @33
    @7
    vb
    cv
    #
    cL
    cfv
    #
    wceq
    #
    vb
    cz
    wrex
    #
    wa
    #
    @14
    @2
    @29
    @33
    @28
    @58
    @39
    @2
    @35
    @28
    @58
    @38
    vb
    cz
    cB
    @7
    cL
    foelrn
    sylan
    anim12dan
    @2
    @59
    @14
    @59
    @32
    @57
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    @2
    @14
    @32
    @57
    va
    vb
    cz
    cz
    reeanv
    @2
    @60
    @14
    va
    vb
    cz
    cz
    @2
    @40
    @55
    cz
    wcel
    #
    wa
    #
    wa
    #
    @14
    @60
    @31
    @56
    @8
    co
    #
    cX
    cfv
    #
    @42
    @56
    cX
    cfv
    #
    cmul
    co
    #
    wceq
    @63
    @30
    @55
    cmul
    co
    #
    cN
    clgs
    co
    #
    @43
    @55
    cN
    clgs
    co
    #
    cmul
    co
    #
    @65
    @67
    @63
    @40
    @61
    @36
    @69
    @71
    wceq
    @2
    @40
    @40
    @61
    @46
    adantrr
    #
    @2
    @40
    @61
    simprr
    #
    @2
    @36
    @62
    @37
    adantr
    @30
    @55
    cN
    lgsdirnn0
    syl3anc
    @63
    @68
    cL
    cfv
    #
    cX
    cfv
    #
    @65
    @69
    @63
    @74
    @64
    cX
    @63
    cL
    zring
    cZ
    crh
    co
    wcel
    #
    @40
    @61
    @74
    @64
    wceq
    @63
    cZ
    crg
    wcel
    #
    @76
    @2
    @77
    @62
    @2
    cZ
    ccrg
    wcel
    #
    @77
    @2
    @36
    @78
    @37
    cN
    cZ
    lgsdchr.z
    zncrng
    syl
    cZ
    crngring
    syl
    #
    adantr
    cZ
    cL
    lgsdchr.l
    zrhrhm
    syl
    @72
    @73
    @30
    @55
    zring
    cZ
    cmul
    @8
    cL
    cz
    zringbas
    zringmulr
    @8
    eqid
    rhmmul
    syl3anc
    fveq2d
    @62
    @2
    @68
    cz
    wcel
    @75
    @69
    wceq
    @30
    @55
    zmulcl
    vy
    @68
    cB
    cD
    vh
    vm
    cG
    cL
    cN
    cX
    cZ
    lgsdchr.g
    lgsdchr.z
    lgsdchr.d
    lgsdchr.b
    lgsdchr.l
    lgsdchr.x
    lgsdchrval
    sylan2
    eqtr3d
    @63
    @42
    @43
    @66
    @70
    cmul
    @2
    @40
    @42
    @43
    wceq
    @61
    @44
    adantrr
    @2
    @61
    @66
    @70
    wceq
    @40
    vy
    @55
    cB
    cD
    vh
    vm
    cG
    cL
    cN
    cX
    cZ
    lgsdchr.g
    lgsdchr.z
    lgsdchr.d
    lgsdchr.b
    lgsdchr.l
    lgsdchr.x
    lgsdchrval
    adantrl
    oveq12d
    3eqtr4d
    @60
    @10
    @65
    @13
    @67
    @60
    @9
    @64
    cX
    @6
    @31
    @7
    @56
    @8
    oveq12
    fveq2d
    @32
    @57
    @11
    @42
    @12
    @66
    cmul
    @49
    @7
    @56
    cX
    fveq2
    oveqan12d
    eqeq12d
    syl5ibrcom
    rexlimdvva
    syl5bir
    imp
    syldan
    ralrimivva
    @51
    @53
    @16
    vx
    cB
    wral
    @17
    @51
    @52
    @16
    vx
    cB
    @14
    vy
    @15
    cB
    ssralv
    ralimdv
    @16
    vx
    @15
    cB
    ssralv
    syld
    mpsyl
    @2
    c1
    cL
    cfv
    #
    cX
    cfv
    #
    c1
    cN
    clgs
    co
    #
    @19
    c1
    @2
    c1
    cz
    wcel
    @81
    @82
    wceq
    1z
    vy
    c1
    cB
    cD
    vh
    vm
    cG
    cL
    cN
    cX
    cZ
    lgsdchr.g
    lgsdchr.z
    lgsdchr.d
    lgsdchr.b
    lgsdchr.l
    lgsdchr.x
    lgsdchrval
    mpan2
    @2
    @80
    @18
    cX
    @2
    @77
    @80
    @18
    wceq
    @79
    cZ
    @18
    cL
    lgsdchr.l
    @18
    eqid
    zrh1
    syl
    fveq2d
    @2
    @45
    @82
    c1
    wceq
    @0
    @45
    @1
    @47
    adantr
    cN
    1lgs
    syl
    3eqtr3d
    @2
    @23
    vx
    cB
    @2
    @29
    @33
    @23
    @39
    @2
    @33
    @23
    @2
    @32
    @23
    va
    cz
    @41
    @23
    @32
    @42
    cc0
    wne
    #
    @31
    @15
    wcel
    #
    wi
    @41
    @43
    cc0
    wne
    #
    @30
    cN
    cgcd
    co
    c1
    wceq
    #
    @83
    @84
    @41
    @85
    @86
    @41
    @40
    @45
    @85
    @86
    wb
    @46
    @48
    @30
    cN
    lgsne0
    syl2anc
    biimpd
    @41
    @42
    @43
    cc0
    @44
    neeq1d
    @2
    @36
    @40
    @84
    @86
    wb
    @37
    @30
    @15
    cL
    cN
    cZ
    lgsdchr.z
    @54
    lgsdchr.l
    znunit
    sylan
    3imtr4d
    @32
    @21
    @83
    @22
    @84
    @32
    @11
    @42
    cc0
    @49
    neeq1d
    @6
    @31
    @15
    eleq1
    imbi12d
    syl5ibrcom
    rexlimdva
    imp
    syldan
    ralrimiva
    3jca
    @2
    vx
    vy
    cB
    cD
    @15
    cG
    cN
    cX
    cZ
    lgsdchr.g
    lgsdchr.z
    lgsdchr.b
    @54
    @0
    @1
    simpl
    lgsdchr.d
    dchrelbas3
    mpbir2and
    @50
    jca
end
