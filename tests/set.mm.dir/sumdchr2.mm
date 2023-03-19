include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "eqeq2.mm"
include "wa.mm"
include "c1.mm"
include "wcel.mm"
include "fveq2.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "dchrmhm.mm"
include "simpr.mm"
include "sseldi.mm"
include "eqid.mm"
include "ringidval.mm"
include "cnfld1.mm"
include "mhm0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "an32s.mm"
include "sumeq2dv.mm"
include "cmul.mm"
include "cfn.mm"
include "cc.mm"
include "cn.mm"
include "dchrfi.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "sylancl.mm"
include "cn0.mm"
include "hashcl.mm"
include "3syl.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "adantr.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "dchrpt.mm"
include "cmin.mm"
include "dchrf.mm"
include "ffvelrnd.mm"
include "fsumcl.mm"
include "0cnd.mm"
include "simprl.mm"
include "subcl.mm"
include "simprr.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "cplusg.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "cbvsumv.mm"
include "cof.mm"
include "dchrmul.mm"
include "wfn.mm"
include "cvv.mm"
include "wf.mm"
include "ffn.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "syl5eq.mm"
include "cmpt.mm"
include "fveq1.mm"
include "cgrp.mm"
include "wf1o.mm"
include "cabl.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "grplactf1o.mm"
include "syl2anc.mm"
include "grplactval.mm"
include "sylan.mm"
include "fsumf1o.mm"
include "fsummulc2.mm"
include "3eqtr4rd.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "subidd.mm"
include "subdird.mm"
include "mul01d.mm"
include "3eqtr4d.mm"
include "mulcanad.mm"
include "rexlimddv.mm"
include "sylan2br.mm"
include "ifbothda.mm"

theorem sumdchr2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let c.1: class .1.
  let cG: class G
  let cN: class N
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  assume sumdchr.g: |- G = ( DChr ` N )
  assume sumdchr.d: |- D = ( Base ` G )
  assume sumdchr2.z: |- Z = ( Z/nZ ` N )
  assume sumdchr2.1: |- .1. = ( 1r ` Z )
  assume sumdchr2.b: |- B = ( Base ` Z )
  assume sumdchr2.n: |- ( ph -> N e. NN )
  assume sumdchr2.x: |- ( ph -> A e. B )

  disjoint .1. x
  disjoint A x
  disjoint D x
  disjoint N x
  disjoint G x
  disjoint ph x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .1. y
  disjoint .1. z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint D a
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint D b
  disjoint D y
  disjoint D z
  disjoint N a
  disjoint N y
  disjoint G a
  disjoint G b
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint Z y
  assert |- ( ph -> sum_ x e. D ( x ` A ) = if ( A = .1. , ( # ` D ) , 0 ) )

  proof
    cA
    c.1
    wceq
    #
    cD
    cA
    vx
    cv
    #
    cfv
    #
    vx
    csu
    #
    cD
    chash
    cfv
    #
    wceq
    @3
    cc0
    wceq
    #
    @3
    @0
    @4
    cc0
    cif
    #
    wceq
    wph
    @4
    cc0
    @4
    @6
    @3
    eqeq2
    cc0
    @6
    @3
    eqeq2
    wph
    @0
    wa
    #
    @3
    cD
    c1
    vx
    csu
    #
    @4
    @7
    cD
    @2
    c1
    vx
    wph
    @1
    cD
    wcel
    #
    @0
    @2
    c1
    wceq
    @0
    wph
    @9
    wa
    #
    @2
    c.1
    @1
    cfv
    #
    c1
    cA
    c.1
    @1
    fveq2
    @10
    @1
    cZ
    cmgp
    cfv
    #
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    @11
    c1
    wceq
    @10
    cD
    @14
    @1
    cD
    cG
    cN
    cZ
    sumdchr.g
    sumdchr2.z
    sumdchr.d
    dchrmhm
    wph
    @9
    simpr
    sseldi
    @12
    @13
    @1
    c1
    c.1
    cZ
    c.1
    @12
    @12
    eqid
    sumdchr2.1
    ringidval
    ccnfld
    c1
    @13
    @13
    eqid
    cnfld1
    ringidval
    mhm0
    syl
    sylan9eqr
    an32s
    sumeq2dv
    wph
    @8
    @4
    wceq
    @0
    wph
    @8
    @4
    c1
    cmul
    co
    #
    @4
    wph
    cD
    cfn
    wcel
    #
    c1
    cc
    wcel
    #
    @8
    @15
    wceq
    wph
    cN
    cn
    wcel
    #
    @16
    sumdchr2.n
    cD
    cG
    cN
    sumdchr.g
    sumdchr.d
    dchrfi
    #
    syl
    ax-1cn
    cD
    c1
    vx
    fsumconst
    sylancl
    wph
    @4
    wph
    @4
    wph
    @18
    @16
    @4
    cn0
    wcel
    sumdchr2.n
    @19
    cD
    hashcl
    3syl
    nn0cnd
    mulid1d
    eqtrd
    adantr
    eqtrd
    @0
    wn
    wph
    cA
    c.1
    wne
    #
    @5
    cA
    c.1
    df-ne
    wph
    @20
    wa
    #
    cA
    vy
    cv
    #
    cfv
    #
    c1
    wne
    #
    @5
    vy
    cD
    @21
    vy
    cA
    cB
    cD
    c.1
    cG
    cN
    cZ
    sumdchr.g
    sumdchr2.z
    sumdchr.d
    sumdchr2.b
    sumdchr2.1
    wph
    @18
    @20
    sumdchr2.n
    adantr
    #
    wph
    @20
    simpr
    wph
    cA
    cB
    wcel
    #
    @20
    sumdchr2.x
    adantr
    #
    dchrpt
    @21
    @22
    cD
    wcel
    #
    @24
    wa
    #
    wa
    #
    @3
    cc0
    @23
    c1
    cmin
    co
    #
    @30
    cD
    @2
    vx
    @30
    @18
    @16
    @21
    @18
    @29
    @25
    adantr
    #
    @19
    syl
    #
    @30
    @9
    wa
    #
    cB
    cc
    cA
    @1
    @34
    cB
    cD
    cG
    cN
    @1
    cZ
    sumdchr.g
    sumdchr2.z
    sumdchr.d
    sumdchr2.b
    @30
    @9
    simpr
    #
    dchrf
    #
    @30
    @26
    @9
    @21
    @26
    @29
    @27
    adantr
    #
    adantr
    #
    ffvelrnd
    #
    fsumcl
    #
    @30
    0cnd
    @30
    @23
    cc
    wcel
    #
    @17
    @31
    cc
    wcel
    @30
    cB
    cc
    cA
    @22
    @30
    cB
    cD
    cG
    cN
    @22
    cZ
    sumdchr.g
    sumdchr2.z
    sumdchr.d
    sumdchr2.b
    @21
    @28
    @24
    simprl
    #
    dchrf
    #
    @37
    ffvelrnd
    #
    ax-1cn
    @23
    c1
    subcl
    sylancl
    #
    @30
    @31
    cc0
    wne
    @24
    @21
    @28
    @24
    simprr
    @30
    @31
    cc0
    @23
    c1
    @30
    @41
    @17
    @31
    cc0
    wceq
    @23
    c1
    wceq
    wb
    @44
    ax-1cn
    @23
    c1
    subeq0
    sylancl
    necon3bid
    mpbird
    @30
    @23
    @3
    cmul
    co
    #
    c1
    @3
    cmul
    co
    #
    cmin
    co
    #
    cc0
    @31
    @3
    cmul
    co
    @31
    cc0
    cmul
    co
    @30
    @48
    @3
    @3
    cmin
    co
    cc0
    @30
    @46
    @3
    @47
    @3
    cmin
    @30
    cD
    cA
    @22
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cfv
    #
    vz
    csu
    #
    cD
    @23
    @2
    cmul
    co
    #
    vx
    csu
    #
    @3
    @46
    @30
    @53
    cD
    cA
    @22
    @1
    @50
    co
    #
    cfv
    #
    vx
    csu
    @55
    cD
    @52
    @57
    vz
    vx
    @49
    @1
    wceq
    cA
    @51
    @56
    @49
    @1
    @22
    @50
    oveq2
    fveq1d
    cbvsumv
    @30
    cD
    @57
    @54
    vx
    @34
    @57
    cA
    @22
    @1
    cmul
    cof
    co
    #
    cfv
    #
    @54
    @34
    cA
    @56
    @58
    @34
    cD
    @50
    cG
    cN
    @22
    @1
    cZ
    sumdchr.g
    sumdchr2.z
    sumdchr.d
    @50
    eqid
    #
    @30
    @28
    @9
    @42
    adantr
    @35
    dchrmul
    fveq1d
    @34
    @22
    cB
    wfn
    #
    @1
    cB
    wfn
    #
    cB
    cvv
    wcel
    #
    @26
    @59
    @54
    wceq
    @34
    cB
    cc
    @22
    wf
    #
    @61
    @30
    @64
    @9
    @43
    adantr
    cB
    cc
    @22
    ffn
    syl
    @34
    cB
    cc
    @1
    wf
    @62
    @36
    cB
    cc
    @1
    ffn
    syl
    @63
    @34
    cB
    cZ
    cbs
    cfv
    cvv
    sumdchr2.b
    cZ
    cbs
    fvex
    eqeltri
    a1i
    @38
    cB
    cmul
    @22
    @1
    cvv
    cA
    fnfvof
    syl22anc
    eqtrd
    sumeq2dv
    syl5eq
    @30
    cD
    @2
    cD
    @52
    vx
    vz
    @22
    va
    cD
    vb
    cD
    va
    cv
    vb
    cv
    @50
    co
    cmpt
    cmpt
    #
    cfv
    #
    @51
    cA
    @1
    @51
    fveq1
    @33
    @30
    cG
    cgrp
    wcel
    #
    @28
    cD
    cD
    @66
    wf1o
    @30
    @18
    cG
    cabl
    wcel
    @67
    @32
    cG
    cN
    sumdchr.g
    dchrabl
    cG
    ablgrp
    3syl
    @42
    @22
    @50
    va
    @65
    cG
    cD
    vb
    @65
    eqid
    #
    sumdchr.d
    @60
    grplactf1o
    syl2anc
    @30
    @28
    @49
    cD
    wcel
    @49
    @66
    cfv
    @51
    wceq
    @42
    @22
    @49
    @50
    va
    @65
    cG
    cD
    vb
    @68
    sumdchr.d
    grplactval
    sylan
    @39
    fsumf1o
    @30
    cD
    @2
    @23
    vx
    @33
    @44
    @39
    fsummulc2
    3eqtr4rd
    @30
    @3
    @40
    mulid2d
    oveq12d
    @30
    @3
    @40
    subidd
    eqtrd
    @30
    @23
    c1
    @3
    @44
    @17
    @30
    ax-1cn
    a1i
    @40
    subdird
    @30
    @31
    @45
    mul01d
    3eqtr4d
    mulcanad
    rexlimddv
    sylan2br
    ifbothda
end
