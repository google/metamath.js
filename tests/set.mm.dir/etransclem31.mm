include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cfa.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cif.mm"
include "cc.mm"
include "etransclem30.mm"
include "wceq.mm"
include "fveq2.mm"
include "prodeq2ad.mm"
include "oveq2d.mm"
include "sumeq2ad.mm"
include "adantl.mm"
include "etransclem16.mm"
include "wcel.mm"
include "wa.mm"
include "faccld.mm"
include "nncnd.mm"
include "adantr.mm"
include "fzfid.mm"
include "cn0.mm"
include "fzssnn0.mm"
include "cmap.mm"
include "wf.mm"
include "crab.mm"
include "ssrab2.mm"
include "simpr.mm"
include "etransclem12.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "fprodcl.mm"
include "nnne0d.mm"
include "fprodn0.mm"
include "divcld.mm"
include "cr.mm"
include "cpr.mm"
include "ad2antrr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cn.mm"
include "cmpt.mm"
include "etransclem5.mm"
include "eqtri.mm"
include "etransclem20.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "fvmptd.mm"
include "caddc.mm"
include "etransclem21.mm"
include "prodeq2dv.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eqeltrrd.mm"
include "iftrue.mm"
include "breq12d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "ifbieq2d.mm"
include "fprod1p.mm"
include "dvdmsscn.mm"
include "sseldd.mm"
include "subid1d.mm"
include "oveq1d.mm"
include "ifeq2d.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "prodeq1i.mm"
include "0red.mm"
include "1red.mm"
include "elfzelz.mm"
include "zred.mm"
include "0lt1.mm"
include "a1i.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "breq1d.mm"
include "prodeq2i.mm"
include "3eqtrd.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"

theorem etransclem31
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vk: setvar k
  let vy: setvar y
  assume etransclem31.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem31.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem31.p: |- ( ph -> P e. NN )
  assume etransclem31.m: |- ( ph -> M e. NN0 )
  assume etransclem31.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem31.n: |- ( ph -> N e. NN0 )
  assume etransclem31.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem31.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )
  assume etransclem31.y: |- ( ph -> Y e. X )

  disjoint C c
  disjoint C j
  disjoint C x
  disjoint c j
  disjoint c x
  disjoint j x
  disjoint H c
  disjoint H j
  disjoint H n
  disjoint H x
  disjoint c n
  disjoint j n
  disjoint n x
  disjoint M c
  disjoint M j
  disjoint M x
  disjoint M n
  disjoint N c
  disjoint N j
  disjoint N x
  disjoint N n
  disjoint P j
  disjoint P x
  disjoint S c
  disjoint S j
  disjoint S n
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint X n
  disjoint Y c
  disjoint Y j
  disjoint Y x
  disjoint c ph
  disjoint j ph
  disjoint ph x
  disjoint n ph
  disjoint C k
  disjoint C y
  disjoint c k
  disjoint c y
  disjoint j k
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint M k
  disjoint M y
  disjoint N k
  disjoint N y
  disjoint P k
  disjoint P y
  disjoint S y
  disjoint X k
  disjoint X y
  disjoint Y y
  disjoint k ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( ( ( S Dn F ) ` N ) ` Y ) = sum_ c e. ( C ` N ) ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( c ` j ) ) ) x. ( if ( ( P - 1 ) < ( c ` 0 ) , 0 , ( ( ( ! ` ( P - 1 ) ) / ( ! ` ( ( P - 1 ) - ( c ` 0 ) ) ) ) x. ( Y ^ ( ( P - 1 ) - ( c ` 0 ) ) ) ) ) x. prod_ j e. ( 1 ... M ) if ( P < ( c ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( c ` j ) ) ) ) x. ( ( Y - j ) ^ ( P - ( c ` j ) ) ) ) ) ) ) )

  proof
    wph
    cY
    cN
    cS
    cF
    cdvn
    co
    cfv
    #
    cfv
    cN
    cC
    cfv
    #
    cN
    cfa
    cfv
    #
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    vc
    cv
    #
    cfv
    #
    cfa
    cfv
    #
    vj
    cprod
    #
    cdiv
    co
    #
    @3
    cY
    @6
    cS
    @4
    cH
    cfv
    cdvn
    co
    cfv
    #
    cfv
    #
    vj
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    @1
    @9
    cP
    c1
    cmin
    co
    #
    cc0
    @5
    cfv
    #
    clt
    wbr
    #
    cc0
    @15
    cfa
    cfv
    #
    @15
    @16
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cY
    @19
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    c1
    cM
    cfz
    co
    #
    cP
    @6
    clt
    wbr
    #
    cc0
    cP
    cfa
    cfv
    #
    cP
    @6
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cY
    @4
    cmin
    co
    #
    @28
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    #
    cmul
    co
    #
    cmul
    co
    #
    vc
    csu
    wph
    vx
    cY
    @1
    @9
    @3
    vx
    cv
    #
    @10
    cfv
    #
    vj
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    @14
    cX
    @0
    cc
    wph
    vx
    cC
    cP
    cS
    vj
    vn
    cF
    cH
    cM
    cN
    cX
    vc
    etransclem31.s
    etransclem31.x
    etransclem31.p
    etransclem31.m
    etransclem31.f
    etransclem31.n
    etransclem31.h
    etransclem31.c
    etransclem30
    @38
    cY
    wceq
    #
    @42
    @14
    wceq
    wph
    @43
    @1
    @41
    @13
    vc
    @43
    @40
    @12
    @9
    cmul
    @43
    @3
    @39
    @11
    vj
    @38
    cY
    @10
    fveq2
    prodeq2ad
    oveq2d
    sumeq2ad
    adantl
    etransclem31.y
    wph
    @1
    @13
    vc
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem31.c
    etransclem31.n
    etransclem16
    wph
    @5
    @1
    wcel
    #
    wa
    #
    @9
    @12
    @45
    @2
    @8
    wph
    @2
    cc
    wcel
    @44
    wph
    @2
    wph
    cN
    etransclem31.n
    faccld
    nncnd
    adantr
    @45
    @3
    @7
    vj
    @45
    cc0
    cM
    fzfid
    #
    @45
    @4
    @3
    wcel
    #
    wa
    #
    @7
    @48
    @6
    @48
    cc0
    cN
    cfz
    co
    #
    cn0
    @6
    cN
    fzssnn0
    @48
    @3
    @49
    @4
    @5
    @48
    @5
    @49
    @3
    cmap
    co
    #
    wcel
    #
    @3
    @49
    @5
    wf
    @45
    @51
    @47
    @45
    @3
    @6
    vj
    csu
    cN
    wceq
    #
    vc
    @50
    crab
    #
    @50
    @5
    @52
    vc
    @50
    ssrab2
    @45
    @5
    @1
    @53
    wph
    @44
    simpr
    wph
    @1
    @53
    wceq
    @44
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem31.c
    etransclem31.n
    etransclem12
    adantr
    eleqtrd
    sseldi
    adantr
    @5
    @49
    @3
    elmapi
    syl
    @45
    @47
    simpr
    #
    ffvelrnd
    sseldi
    #
    faccld
    #
    nncnd
    #
    fprodcl
    @45
    @3
    @7
    vj
    @46
    @57
    @48
    @7
    @56
    nnne0d
    fprodn0
    divcld
    @45
    @3
    @11
    vj
    @46
    @48
    cX
    cc
    cY
    @10
    @48
    vy
    cP
    cS
    vk
    cH
    @4
    cM
    @6
    cX
    wph
    cS
    cr
    cc
    cpr
    wcel
    @44
    @47
    etransclem31.s
    ad2antrr
    #
    wph
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    wcel
    @44
    @47
    etransclem31.x
    ad2antrr
    #
    wph
    cP
    cn
    wcel
    @44
    @47
    etransclem31.p
    ad2antrr
    #
    cH
    vj
    @3
    vx
    cX
    @38
    @4
    cmin
    co
    @4
    cc0
    wceq
    #
    @15
    cP
    cif
    #
    cexp
    co
    cmpt
    cmpt
    vk
    @3
    vy
    cX
    vy
    cv
    vk
    cv
    #
    cmin
    co
    @63
    cc0
    wceq
    @15
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    etransclem31.h
    vx
    vy
    cP
    vj
    vk
    cM
    cX
    etransclem5
    eqtri
    #
    @54
    @55
    etransclem20
    wph
    cY
    cX
    wcel
    @44
    @47
    etransclem31.y
    ad2antrr
    #
    ffvelrnd
    #
    fprodcl
    mulcld
    fsumcl
    fvmptd
    wph
    @1
    @13
    @37
    vc
    @45
    @12
    @36
    @9
    cmul
    @45
    @12
    @3
    @62
    @6
    clt
    wbr
    #
    cc0
    @62
    cfa
    cfv
    #
    @62
    @6
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    @31
    @69
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    @17
    cc0
    @21
    cY
    cc0
    cmin
    co
    #
    @19
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    @74
    vj
    cprod
    #
    cmul
    co
    #
    @36
    @45
    @3
    @11
    @74
    vj
    @48
    vy
    cP
    cS
    vk
    cH
    @4
    cM
    @6
    cX
    cY
    @58
    @59
    @60
    @64
    @54
    @55
    @65
    etransclem21
    #
    prodeq2dv
    @45
    @74
    @78
    vj
    cc0
    cM
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    @44
    wph
    cM
    cn0
    @84
    etransclem31.m
    nn0uz
    syl6eleq
    adantr
    @48
    @11
    @74
    cc
    @83
    @66
    eqeltrrd
    @61
    @67
    @17
    @73
    @77
    cc0
    @61
    @62
    @15
    @6
    @16
    clt
    @61
    @15
    cP
    iftrue
    #
    @4
    cc0
    @5
    fveq2
    #
    breq12d
    @61
    @71
    @21
    @72
    @76
    cmul
    @61
    @68
    @18
    @70
    @20
    cdiv
    @61
    @62
    @15
    cfa
    @85
    fveq2d
    @61
    @69
    @19
    cfa
    @61
    @62
    @15
    @6
    @16
    cmin
    @85
    @86
    oveq12d
    #
    fveq2d
    oveq12d
    @61
    @31
    @75
    @69
    @19
    cexp
    @4
    cc0
    cY
    cmin
    oveq2
    @87
    oveq12d
    oveq12d
    ifbieq2d
    fprod1p
    wph
    @82
    @36
    wceq
    @44
    wph
    @78
    @24
    @81
    @35
    cmul
    wph
    @17
    @77
    @23
    cc0
    wph
    @76
    @22
    @21
    cmul
    wph
    @75
    cY
    @19
    cexp
    wph
    cY
    wph
    cX
    cc
    cY
    wph
    cS
    cX
    etransclem31.s
    etransclem31.x
    dvdmsscn
    etransclem31.y
    sseldd
    subid1d
    oveq1d
    oveq2d
    ifeq2d
    @81
    @35
    wceq
    wph
    @81
    @25
    @74
    vj
    cprod
    @35
    @80
    @25
    @74
    vj
    @79
    c1
    cM
    cfz
    0p1e1
    oveq1i
    prodeq1i
    @25
    @74
    @34
    vj
    @4
    @25
    wcel
    #
    @67
    @26
    @73
    @33
    cc0
    @88
    @62
    cP
    @6
    clt
    @88
    @61
    @15
    cP
    @88
    @4
    cc0
    @88
    @4
    @88
    cc0
    c1
    @4
    @88
    0red
    @88
    1red
    @88
    @4
    @4
    c1
    cM
    elfzelz
    zred
    cc0
    c1
    clt
    wbr
    @88
    0lt1
    a1i
    @4
    c1
    cM
    elfzle1
    ltletrd
    gt0ne0d
    neneqd
    iffalsed
    #
    breq1d
    @88
    @71
    @30
    @72
    @32
    cmul
    @88
    @68
    @27
    @70
    @29
    cdiv
    @88
    @62
    cP
    cfa
    @89
    fveq2d
    @88
    @69
    @28
    cfa
    @88
    @62
    cP
    @6
    cmin
    @89
    oveq1d
    #
    fveq2d
    oveq12d
    @88
    @69
    @28
    @31
    cexp
    @90
    oveq2d
    oveq12d
    ifbieq2d
    prodeq2i
    eqtri
    a1i
    oveq12d
    adantr
    3eqtrd
    oveq2d
    sumeq2dv
    eqtrd
end
