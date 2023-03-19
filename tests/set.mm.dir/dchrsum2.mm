include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cphi.mm"
include "cc0.mm"
include "cif.mm"
include "eqeq2.mm"
include "wa.mm"
include "c1.mm"
include "wcel.mm"
include "fveq1.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "dchr1.mm"
include "sylan9eqr.mm"
include "an32s.mm"
include "sumeq2dv.mm"
include "chash.mm"
include "cmul.mm"
include "co.mm"
include "cfn.mm"
include "cc.mm"
include "cn0.mm"
include "znunithash.mm"
include "phicld.mm"
include "nnnn0d.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "wn.mm"
include "wrex.mm"
include "wral.mm"
include "cabl.mm"
include "cgrp.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "grpidcl.mm"
include "4syl.mm"
include "dchreq.mm"
include "notbid.mm"
include "rexnal.mm"
include "syl6bbr.mm"
include "wne.mm"
include "df-ne.mm"
include "neeq2d.mm"
include "cmin.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "dchrf.mm"
include "unitss.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "adantlr.mm"
include "fsumcl.mm"
include "0cnd.mm"
include "simprl.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "subcl.mm"
include "simprr.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "cmulr.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvsumv.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "dchrmhm.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cnfldmul.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "cmpt.mm"
include "fveq2.mm"
include "cress.mm"
include "wf1o.mm"
include "ccrg.mm"
include "crg.mm"
include "zncrng.mm"
include "crngring.mm"
include "unitgrp.mm"
include "unitgrpbas.mm"
include "cplusg.mm"
include "ressplusg.mm"
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
include "1cnd.mm"
include "subdird.mm"
include "mul01d.mm"
include "3eqtr4d.mm"
include "mulcanad.mm"
include "expr.mm"
include "sylbid.mm"
include "syl5bir.mm"
include "rexlimdva.mm"
include "imp.mm"
include "ifbothda.mm"

theorem dchrsum2
  let wph: wff ph
  let cD: class D
  let cU: class U
  let c.1: class .1.
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vk: setvar k
  let cB: class B
  let vx: setvar x
  let vb: setvar b
  let vc: setvar c
  assume dchrsum.g: |- G = ( DChr ` N )
  assume dchrsum.z: |- Z = ( Z/nZ ` N )
  assume dchrsum.d: |- D = ( Base ` G )
  assume dchrsum.1: |- .1. = ( 0g ` G )
  assume dchrsum.x: |- ( ph -> X e. D )
  assume dchrsum2.u: |- U = ( Unit ` Z )

  disjoint .1. a
  disjoint a ph
  disjoint U a
  disjoint X a
  disjoint Z a
  disjoint a k
  disjoint .1. k
  disjoint B a
  disjoint a x
  disjoint k x
  disjoint k ph
  disjoint ph x
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint b k
  disjoint b x
  disjoint U b
  disjoint c k
  disjoint c x
  disjoint U c
  disjoint U k
  disjoint U x
  disjoint X k
  disjoint X x
  disjoint Z b
  disjoint Z c
  disjoint Z k
  disjoint Z x
  assert |- ( ph -> sum_ a e. U ( X ` a ) = if ( X = .1. , ( phi ` N ) , 0 ) )

  proof
    cX
    c.1
    wceq
    #
    cU
    va
    cv
    #
    cX
    cfv
    #
    va
    csu
    #
    cN
    cphi
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
    cU
    c1
    va
    csu
    #
    @4
    @7
    cU
    @2
    c1
    va
    wph
    @1
    cU
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
    @1
    c.1
    cfv
    c1
    @1
    cX
    c.1
    fveq1
    @10
    @1
    cU
    c.1
    cG
    cN
    cZ
    dchrsum.g
    dchrsum.z
    dchrsum.1
    dchrsum2.u
    wph
    cN
    cn
    wcel
    #
    @9
    wph
    cX
    cD
    wcel
    @11
    dchrsum.x
    cD
    cG
    cN
    cX
    dchrsum.g
    dchrsum.d
    dchrrcl
    syl
    #
    adantr
    wph
    @9
    simpr
    dchr1
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
    cU
    chash
    cfv
    #
    c1
    cmul
    co
    #
    @4
    c1
    cmul
    co
    @4
    wph
    cU
    cfn
    wcel
    #
    c1
    cc
    wcel
    #
    @8
    @14
    wceq
    wph
    @13
    cn0
    wcel
    #
    @15
    wph
    @13
    @4
    cn0
    wph
    @11
    @13
    @4
    wceq
    @12
    cU
    cN
    cZ
    dchrsum.z
    dchrsum2.u
    znunithash
    syl
    #
    wph
    @4
    wph
    cN
    @12
    phicld
    #
    nnnn0d
    eqeltrd
    cU
    cvv
    wcel
    #
    @15
    @17
    wb
    cU
    cZ
    cui
    cfv
    cvv
    dchrsum2.u
    cZ
    cui
    fvex
    eqeltri
    #
    cU
    cvv
    hashclb
    ax-mp
    sylibr
    #
    ax-1cn
    cU
    c1
    va
    fsumconst
    sylancl
    wph
    @13
    @4
    c1
    cmul
    @18
    oveq1d
    wph
    @4
    wph
    @4
    @19
    nncnd
    mulid1d
    3eqtrd
    adantr
    eqtrd
    wph
    @0
    wn
    #
    @5
    wph
    @23
    vk
    cv
    #
    cX
    cfv
    #
    @24
    c.1
    cfv
    #
    wceq
    #
    wn
    #
    vk
    cU
    wrex
    #
    @5
    wph
    @23
    @27
    vk
    cU
    wral
    #
    wn
    @29
    wph
    @0
    @30
    wph
    cD
    cU
    vk
    cG
    cN
    cX
    c.1
    cZ
    dchrsum.g
    dchrsum.z
    dchrsum.d
    dchrsum2.u
    dchrsum.x
    wph
    @11
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    c.1
    cD
    wcel
    @12
    cG
    cN
    dchrsum.g
    dchrabl
    cG
    ablgrp
    cD
    cG
    c.1
    dchrsum.d
    dchrsum.1
    grpidcl
    4syl
    dchreq
    notbid
    @27
    vk
    cU
    rexnal
    syl6bbr
    wph
    @28
    @5
    vk
    cU
    @28
    @25
    @26
    wne
    #
    wph
    @24
    cU
    wcel
    #
    wa
    #
    @5
    @25
    @26
    df-ne
    @33
    @31
    @25
    c1
    wne
    #
    @5
    @33
    @26
    c1
    @25
    @33
    @24
    cU
    c.1
    cG
    cN
    cZ
    dchrsum.g
    dchrsum.z
    dchrsum.1
    dchrsum2.u
    wph
    @11
    @32
    @12
    adantr
    wph
    @32
    simpr
    dchr1
    neeq2d
    wph
    @32
    @34
    @5
    wph
    @32
    @34
    wa
    #
    wa
    #
    @3
    cc0
    @25
    c1
    cmin
    co
    #
    @36
    cU
    @2
    va
    wph
    @15
    @35
    @22
    adantr
    #
    wph
    @9
    @2
    cc
    wcel
    #
    @35
    wph
    cZ
    cbs
    cfv
    #
    cc
    cX
    wf
    #
    @1
    @40
    wcel
    #
    @39
    @9
    wph
    @40
    cD
    cG
    cN
    cX
    cZ
    dchrsum.g
    dchrsum.z
    dchrsum.d
    @40
    eqid
    #
    dchrsum.x
    dchrf
    #
    cU
    @40
    @1
    @40
    cZ
    cU
    @43
    dchrsum2.u
    unitss
    #
    sseli
    #
    @40
    cc
    @1
    cX
    ffvelrn
    syl2an
    adantlr
    #
    fsumcl
    #
    @36
    0cnd
    @36
    @25
    cc
    wcel
    #
    @16
    @37
    cc
    wcel
    @36
    @40
    cc
    @24
    cX
    wph
    @41
    @35
    @44
    adantr
    @36
    cU
    @40
    @24
    @45
    wph
    @32
    @34
    simprl
    #
    sseldi
    #
    ffvelrnd
    #
    ax-1cn
    @25
    c1
    subcl
    sylancl
    #
    @36
    @37
    cc0
    wne
    @34
    wph
    @32
    @34
    simprr
    @36
    @37
    cc0
    @25
    c1
    @36
    @49
    @16
    @37
    cc0
    wceq
    @25
    c1
    wceq
    wb
    @52
    ax-1cn
    @25
    c1
    subeq0
    sylancl
    necon3bid
    mpbird
    @36
    @25
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
    @37
    @3
    cmul
    co
    @37
    cc0
    cmul
    co
    @36
    @56
    @3
    @3
    cmin
    co
    cc0
    @36
    @54
    @3
    @55
    @3
    cmin
    @36
    cU
    @24
    vx
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
    vx
    csu
    #
    cU
    @25
    @2
    cmul
    co
    #
    va
    csu
    #
    @3
    @54
    @36
    @61
    cU
    @24
    @1
    @58
    co
    #
    cX
    cfv
    #
    va
    csu
    @63
    cU
    @60
    @65
    vx
    va
    @57
    @1
    wceq
    @59
    @64
    cX
    @57
    @1
    @24
    @58
    oveq2
    fveq2d
    cbvsumv
    @36
    cU
    @65
    @62
    va
    @36
    @9
    wa
    cX
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
    #
    @24
    @40
    wcel
    #
    @42
    @65
    @62
    wceq
    wph
    @69
    @35
    @9
    wph
    cD
    @68
    cX
    cD
    cG
    cN
    cZ
    dchrsum.g
    dchrsum.z
    dchrsum.d
    dchrmhm
    dchrsum.x
    sseldi
    ad2antrr
    @36
    @70
    @9
    @51
    adantr
    @9
    @42
    @36
    @46
    adantl
    @40
    @58
    cmul
    @66
    @67
    cX
    @24
    @1
    @40
    cZ
    @66
    @66
    eqid
    #
    @43
    mgpbas
    cZ
    @58
    @66
    @71
    @58
    eqid
    mgpplusg
    #
    ccnfld
    cmul
    @67
    @67
    eqid
    cnfldmul
    mgpplusg
    mhmlin
    syl3anc
    sumeq2dv
    syl5eq
    @36
    cU
    @2
    cU
    @60
    va
    vx
    @24
    vb
    cU
    vc
    cU
    vb
    cv
    vc
    cv
    @58
    co
    cmpt
    cmpt
    #
    cfv
    #
    @59
    @1
    @59
    cX
    fveq2
    @38
    @36
    @66
    cU
    cress
    co
    #
    cgrp
    wcel
    #
    @32
    cU
    cU
    @74
    wf1o
    wph
    @76
    @35
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    cZ
    crg
    wcel
    @76
    wph
    cN
    @12
    nnnn0d
    cN
    cZ
    dchrsum.z
    zncrng
    cZ
    crngring
    cZ
    cU
    @75
    dchrsum2.u
    @75
    eqid
    #
    unitgrp
    4syl
    adantr
    @50
    @24
    @58
    vb
    @73
    @75
    cU
    vc
    @73
    eqid
    #
    cZ
    cU
    @75
    dchrsum2.u
    @77
    unitgrpbas
    #
    @20
    @58
    @75
    cplusg
    cfv
    wceq
    @21
    cU
    @58
    @66
    @75
    cvv
    @77
    @72
    ressplusg
    ax-mp
    grplactf1o
    syl2anc
    @36
    @32
    @57
    cU
    wcel
    @57
    @74
    cfv
    @59
    wceq
    @50
    @24
    @57
    @58
    vb
    @73
    @75
    cU
    vc
    @78
    @79
    grplactval
    sylan
    @47
    fsumf1o
    @36
    cU
    @2
    @25
    va
    @38
    @52
    @47
    fsummulc2
    3eqtr4rd
    @36
    @3
    @48
    mulid2d
    oveq12d
    @36
    @3
    @48
    subidd
    eqtrd
    @36
    @25
    c1
    @3
    @52
    @36
    1cnd
    @48
    subdird
    @36
    @37
    @53
    mul01d
    3eqtr4d
    mulcanad
    expr
    sylbid
    syl5bir
    rexlimdva
    sylbid
    imp
    ifbothda
end
