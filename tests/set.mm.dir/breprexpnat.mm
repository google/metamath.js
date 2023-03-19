include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "cc0.mm"
include "cmul.mm"
include "crepr.mm"
include "cfv.mm"
include "chash.mm"
include "cfzo.mm"
include "cn.mm"
include "cind.mm"
include "csn.mm"
include "cxp.mm"
include "cprod.mm"
include "wf.mm"
include "cc.mm"
include "cmap.mm"
include "wss.mm"
include "fvex.mm"
include "fconst.mm"
include "wcel.mm"
include "cpr.mm"
include "cvv.mm"
include "nnex.mm"
include "indf.mm"
include "sylancr.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "prssi.mm"
include "mp2an.mm"
include "fss.mm"
include "sylancl.mm"
include "cnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "snss.mm"
include "sylib.mm"
include "breprexp.mm"
include "wa.mm"
include "wceq.mm"
include "fvconst2.mm"
include "ad2antlr.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "a1i.mm"
include "cfn.mm"
include "fzfi.mm"
include "fz1ssnn.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "cn0.mm"
include "nnssnn0.mm"
include "sstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "expcld.mm"
include "indsumin.mm"
include "incom.mm"
include "sumeq1d.mm"
include "3eqtrd.mm"
include "prodeq2dv.mm"
include "fzofi.mm"
include "inss2.mm"
include "ssfi.mm"
include "fsumcl.mm"
include "fprodconst.mm"
include "syl2anc.mm"
include "hashfzo0.mm"
include "syl.mm"
include "oveq2d.mm"
include "cz.mm"
include "fzssz.mm"
include "reprfi.mm"
include "fz0ssnn0.mm"
include "ad3antrrr.mm"
include "reprf.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "fprodcl.mm"
include "fsummulc1.mm"
include "hashreprin.mm"
include "adantl.mm"
include "3eqtr4rd.mm"
include "3eqtr3d.mm"
include "oveq1i.mm"
include "sumeq2i.mm"
include "3eqtr4g.mm"

theorem breprexpnat
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cR: class R
  let cS: class S
  let vm: setvar m
  let cN: class N
  let cZ: class Z
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  let vs: setvar s
  let vt: setvar t
  assume breprexp.n: |- ( ph -> N e. NN0 )
  assume breprexp.s: |- ( ph -> S e. NN0 )
  assume breprexp.z: |- ( ph -> Z e. CC )
  assume breprexpnat.a: |- ( ph -> A C_ NN )
  assume breprexpnat.p: |- P = sum_ b e. ( A i^i ( 1 ... N ) ) ( Z ^ b )
  assume breprexpnat.r: |- R = ( # ` ( ( A i^i ( 1 ... N ) ) ( repr ` S ) m ) )

  disjoint A b
  disjoint A m
  disjoint b m
  disjoint N b
  disjoint N m
  disjoint S b
  disjoint S m
  disjoint Z b
  disjoint Z m
  disjoint b ph
  disjoint m ph
  disjoint N m
  disjoint S m
  disjoint Z m
  disjoint A a
  disjoint A c
  disjoint a b
  disjoint a c
  disjoint a m
  disjoint b c
  disjoint c m
  disjoint N a
  disjoint N c
  disjoint S a
  disjoint S c
  disjoint Z a
  disjoint Z c
  disjoint a ph
  disjoint c ph
  disjoint N c
  disjoint N s
  disjoint N t
  disjoint c m
  disjoint c s
  disjoint c t
  disjoint m s
  disjoint m t
  disjoint s t
  disjoint S a
  disjoint S c
  disjoint S s
  disjoint S t
  disjoint a c
  disjoint a m
  disjoint a s
  disjoint a t
  disjoint Z c
  disjoint Z s
  disjoint Z t
  disjoint b c
  disjoint b s
  disjoint b t
  disjoint c ph
  disjoint ph s
  disjoint ph t
  assert |- ( ph -> ( P ^ S ) = sum_ m e. ( 0 ... ( S x. N ) ) ( R x. ( Z ^ m ) ) )

  proof
    wph
    cA
    c1
    cN
    cfz
    co
    #
    cin
    #
    cZ
    vb
    cv
    #
    cexp
    co
    #
    vb
    csu
    #
    cS
    cexp
    co
    #
    cc0
    cS
    cN
    cmul
    co
    #
    cfz
    co
    #
    @1
    vm
    cv
    #
    cS
    crepr
    cfv
    #
    co
    chash
    cfv
    #
    cZ
    @8
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cP
    cS
    cexp
    co
    @7
    cR
    @11
    cmul
    co
    #
    vm
    csu
    wph
    cc0
    cS
    cfzo
    co
    #
    @0
    @2
    va
    cv
    #
    @15
    cA
    cn
    cind
    cfv
    #
    cfv
    #
    csn
    #
    cxp
    #
    cfv
    #
    cfv
    #
    @3
    cmul
    co
    #
    vb
    csu
    #
    va
    cprod
    #
    @7
    @0
    @8
    @9
    co
    #
    @15
    @16
    vc
    cv
    #
    cfv
    #
    @21
    cfv
    #
    va
    cprod
    #
    @11
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    @5
    @13
    wph
    cS
    vm
    @20
    cN
    cZ
    va
    vb
    vc
    breprexp.n
    breprexp.s
    breprexp.z
    wph
    @15
    @19
    @20
    wf
    @19
    cc
    cn
    cmap
    co
    #
    wss
    #
    @15
    @33
    @20
    wf
    @15
    @18
    cA
    @17
    fvex
    #
    fconst
    wph
    @18
    @33
    wcel
    #
    @34
    wph
    cn
    cc
    @18
    wf
    #
    @36
    wph
    cn
    cc0
    c1
    cpr
    #
    @18
    wf
    #
    @38
    cc
    wss
    #
    @37
    wph
    cn
    cvv
    wcel
    #
    cA
    cn
    wss
    #
    @39
    nnex
    breprexpnat.a
    cA
    cn
    cvv
    indf
    sylancr
    #
    cc0
    cc
    wcel
    c1
    cc
    wcel
    @40
    0cn
    ax-1cn
    cc0
    c1
    cc
    prssi
    mp2an
    #
    cn
    @38
    cc
    @18
    fss
    sylancl
    cc
    cn
    @18
    cnex
    nnex
    elmap
    sylibr
    @18
    @33
    @35
    snss
    sylib
    @15
    @19
    @33
    @20
    fss
    sylancr
    breprexp
    wph
    @25
    @15
    @4
    va
    cprod
    #
    @4
    @15
    chash
    cfv
    #
    cexp
    co
    #
    @5
    wph
    @15
    @24
    @4
    va
    wph
    @16
    @15
    wcel
    #
    wa
    #
    @24
    @0
    @2
    @18
    cfv
    #
    @3
    cmul
    co
    #
    vb
    csu
    @0
    cA
    cin
    #
    @3
    vb
    csu
    @4
    @49
    @0
    @23
    @51
    vb
    @49
    @2
    @0
    wcel
    #
    wa
    #
    @22
    @50
    @3
    cmul
    @54
    @2
    @21
    @18
    @48
    @21
    @18
    wceq
    wph
    @53
    @15
    @18
    @16
    @35
    fvconst2
    #
    ad2antlr
    fveq1d
    oveq1d
    sumeq2dv
    @49
    @0
    cA
    @3
    vb
    cn
    cvv
    @41
    @49
    nnex
    a1i
    @0
    cfn
    wcel
    #
    @49
    c1
    cN
    fzfi
    #
    a1i
    @0
    cn
    wss
    #
    @49
    cN
    fz1ssnn
    #
    a1i
    wph
    @42
    @48
    breprexpnat.a
    adantr
    @54
    cZ
    @2
    wph
    cZ
    cc
    wcel
    #
    @48
    @53
    breprexp.z
    ad2antrr
    @54
    @0
    cn0
    @2
    @0
    cn
    cn0
    @59
    nnssnn0
    sstri
    #
    @49
    @53
    simpr
    sseldi
    expcld
    indsumin
    @49
    @52
    @1
    @3
    vb
    @52
    @1
    wceq
    @49
    @0
    cA
    incom
    a1i
    sumeq1d
    3eqtrd
    prodeq2dv
    wph
    @15
    cfn
    wcel
    #
    @4
    cc
    wcel
    @45
    @47
    wceq
    @62
    wph
    cc0
    cS
    fzofi
    #
    a1i
    wph
    @1
    @3
    vb
    @1
    cfn
    wcel
    #
    wph
    @56
    @1
    @0
    wss
    @64
    @57
    cA
    @0
    inss2
    #
    @0
    @1
    ssfi
    mp2an
    a1i
    wph
    @2
    @1
    wcel
    #
    wa
    #
    cZ
    @2
    wph
    @60
    @66
    breprexp.z
    adantr
    @67
    @1
    cn0
    @2
    @1
    @0
    cn0
    @65
    @61
    sstri
    wph
    @66
    simpr
    sseldi
    expcld
    fsumcl
    @15
    @4
    va
    fprodconst
    syl2anc
    wph
    @46
    cS
    @4
    cexp
    wph
    cS
    cn0
    wcel
    #
    @46
    cS
    wceq
    breprexp.s
    cS
    hashfzo0
    syl
    oveq2d
    3eqtrd
    wph
    @7
    @32
    @12
    vm
    wph
    @8
    @7
    wcel
    #
    wa
    #
    @26
    @15
    @28
    @18
    cfv
    #
    va
    cprod
    #
    vc
    csu
    #
    @11
    cmul
    co
    @26
    @72
    @11
    cmul
    co
    #
    vc
    csu
    @12
    @32
    @70
    @26
    @72
    @11
    vc
    @70
    @0
    cS
    @8
    @58
    @70
    @59
    a1i
    #
    @70
    @7
    cz
    @8
    cc0
    @6
    fzssz
    wph
    @69
    simpr
    #
    sseldi
    #
    wph
    @68
    @69
    breprexp.s
    adantr
    #
    @56
    @70
    @57
    a1i
    #
    reprfi
    @70
    cZ
    @8
    wph
    @60
    @69
    breprexp.z
    adantr
    @70
    @7
    cn0
    @8
    @6
    fz0ssnn0
    @76
    sseldi
    expcld
    @70
    @27
    @26
    wcel
    #
    wa
    #
    @15
    @71
    va
    @62
    @81
    @63
    a1i
    @81
    @48
    wa
    #
    @38
    cc
    @71
    @44
    @82
    cn
    @38
    @28
    @18
    wph
    @39
    @69
    @80
    @48
    @43
    ad3antrrr
    @82
    @0
    cn
    @28
    @59
    @81
    @15
    @0
    @16
    @27
    @81
    @0
    @27
    cS
    @8
    @58
    @81
    @59
    a1i
    @70
    @8
    cz
    wcel
    @80
    @77
    adantr
    @70
    @68
    @80
    @78
    adantr
    @70
    @80
    simpr
    reprf
    ffvelrnda
    sseldi
    ffvelrnd
    sseldi
    fprodcl
    fsummulc1
    @70
    @10
    @73
    @11
    cmul
    @70
    cA
    @0
    cS
    @8
    va
    vc
    wph
    @42
    @69
    breprexpnat.a
    adantr
    @77
    @78
    @79
    @75
    hashreprin
    oveq1d
    @70
    @26
    @31
    @74
    vc
    @81
    @30
    @72
    @11
    cmul
    @70
    @30
    @72
    wceq
    @80
    @70
    @15
    @29
    @71
    va
    @48
    @29
    @71
    wceq
    @70
    @48
    @28
    @21
    @18
    @55
    fveq1d
    adantl
    prodeq2dv
    adantr
    oveq1d
    sumeq2dv
    3eqtr4rd
    sumeq2dv
    3eqtr3d
    cP
    @4
    cS
    cexp
    breprexpnat.p
    oveq1i
    @7
    @14
    @12
    vm
    @14
    @12
    wceq
    @69
    cR
    @10
    @11
    cmul
    breprexpnat.r
    oveq1i
    a1i
    sumeq2i
    3eqtr4g
end
