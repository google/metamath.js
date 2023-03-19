include "c3.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "cneg.mm"
include "wa.mm"
include "cc.mm"
include "wrex.mm"
include "csqrt.mm"
include "cfv.mm"
include "ccxp.mm"
include "wcel.mm"
include "c9.mm"
include "cmin.mm"
include "c7.mm"
include "cdc.mm"
include "2cn.mm"
include "cn0.mm"
include "3nn0.mm"
include "expcl.mm"
include "sylancl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "9cn.mm"
include "mulcld.mm"
include "subcld.mm"
include "2nn0.mm"
include "7nn.mm"
include "decnncl.mm"
include "nncni.mm"
include "sqcld.mm"
include "addcld.mm"
include "eqeltrd.mm"
include "c4.mm"
include "4cn.mm"
include "3cn.mm"
include "sqrtcld.mm"
include "halfcld.mm"
include "3ne0.mm"
include "reccli.mm"
include "cxpcl.mm"
include "oveq1d.mm"
include "cn.mm"
include "3nn.mm"
include "cxproot.mm"
include "eqtrd.mm"
include "sqsqrtd.mm"
include "a1i.mm"
include "wne.mm"
include "4ne0.mm"
include "cz.mm"
include "3z.mm"
include "expne0d.mm"
include "mulne0d.mm"
include "oveq2d.mm"
include "subsq.mm"
include "syl2anc.mm"
include "nncand.mm"
include "3eqtr3d.mm"
include "mul02d.mm"
include "3netr4d.mm"
include "oveq1.mm"
include "necon3i.mm"
include "syl.mm"
include "2ne0.mm"
include "divne0d.mm"
include "cxpne0d.mm"
include "eqnetrd.mm"
include "cubic2.mm"
include "1cubr.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"
include "syl6bbr.mm"

theorem cubic
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cT: class T
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vr: setvar r
  assume cubic.r: |- R = { 1 , ( ( -u 1 + ( _i x. ( sqrt ` 3 ) ) ) / 2 ) , ( ( -u 1 - ( _i x. ( sqrt ` 3 ) ) ) / 2 ) }
  assume cubic.a: |- ( ph -> A e. CC )
  assume cubic.z: |- ( ph -> A =/= 0 )
  assume cubic.b: |- ( ph -> B e. CC )
  assume cubic.c: |- ( ph -> C e. CC )
  assume cubic.d: |- ( ph -> D e. CC )
  assume cubic.x: |- ( ph -> X e. CC )
  assume cubic.t: |- ( ph -> T = ( ( ( N + ( sqrt ` G ) ) / 2 ) ^c ( 1 / 3 ) ) )
  assume cubic.g: |- ( ph -> G = ( ( N ^ 2 ) - ( 4 x. ( M ^ 3 ) ) ) )
  assume cubic.m: |- ( ph -> M = ( ( B ^ 2 ) - ( 3 x. ( A x. C ) ) ) )
  assume cubic.n: |- ( ph -> N = ( ( ( 2 x. ( B ^ 3 ) ) - ( ( 9 x. A ) x. ( B x. C ) ) ) + ( ; 2 7 x. ( ( A ^ 2 ) x. D ) ) ) )
  assume cubic.0: |- ( ph -> M =/= 0 )

  disjoint A r
  disjoint B r
  disjoint M r
  disjoint N r
  disjoint ph r
  disjoint T r
  disjoint X r
  assert |- ( ph -> ( ( ( ( A x. ( X ^ 3 ) ) + ( B x. ( X ^ 2 ) ) ) + ( ( C x. X ) + D ) ) = 0 <-> E. r e. R X = -u ( ( ( B + ( r x. T ) ) + ( M / ( r x. T ) ) ) / ( 3 x. A ) ) ) )

  proof
    wph
    cA
    cX
    c3
    cexp
    co
    cmul
    co
    cB
    cX
    c2
    cexp
    co
    cmul
    co
    caddc
    co
    cC
    cX
    cmul
    co
    cD
    caddc
    co
    caddc
    co
    cc0
    wceq
    vr
    cv
    #
    c3
    cexp
    co
    c1
    wceq
    #
    cX
    cB
    @0
    cT
    cmul
    co
    #
    caddc
    co
    cM
    @2
    cdiv
    co
    caddc
    co
    c3
    cA
    cmul
    co
    cdiv
    co
    cneg
    wceq
    #
    wa
    #
    vr
    cc
    wrex
    @3
    vr
    cR
    wrex
    wph
    cA
    cB
    cC
    cD
    cT
    cG
    csqrt
    cfv
    #
    cM
    cN
    cX
    vr
    cubic.a
    cubic.z
    cubic.b
    cubic.c
    cubic.d
    cubic.x
    wph
    cT
    cN
    @5
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c1
    c3
    cdiv
    co
    #
    ccxp
    co
    #
    cc
    cubic.t
    wph
    @7
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @9
    cc
    wcel
    wph
    @6
    wph
    cN
    @5
    wph
    cN
    c2
    cB
    c3
    cexp
    co
    #
    cmul
    co
    #
    c9
    cA
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c2
    c7
    cdc
    #
    cA
    c2
    cexp
    co
    #
    cD
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    cc
    cubic.n
    wph
    @17
    @21
    wph
    @13
    @16
    wph
    c2
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @13
    cc
    wcel
    2cn
    wph
    cB
    cc
    wcel
    c3
    cn0
    wcel
    #
    @23
    cubic.b
    3nn0
    cB
    c3
    expcl
    sylancl
    c2
    @12
    mulcl
    sylancr
    wph
    @14
    @15
    wph
    c9
    cc
    wcel
    cA
    cc
    wcel
    @14
    cc
    wcel
    9cn
    cubic.a
    c9
    cA
    mulcl
    sylancr
    wph
    cB
    cC
    cubic.b
    cubic.c
    mulcld
    mulcld
    subcld
    wph
    @18
    cc
    wcel
    @20
    cc
    wcel
    @21
    cc
    wcel
    @18
    c2
    c7
    2nn0
    7nn
    decnncl
    nncni
    wph
    @19
    cD
    wph
    cA
    cubic.a
    sqcld
    cubic.d
    mulcld
    @18
    @20
    mulcl
    sylancr
    addcld
    eqeltrd
    #
    wph
    cG
    wph
    cG
    cN
    c2
    cexp
    co
    #
    c4
    cM
    c3
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc
    cubic.g
    wph
    @26
    @28
    wph
    cN
    @25
    sqcld
    #
    wph
    c4
    cc
    wcel
    #
    @27
    cc
    wcel
    #
    @28
    cc
    wcel
    4cn
    wph
    cM
    cc
    wcel
    @24
    @32
    wph
    cM
    cB
    c2
    cexp
    co
    #
    c3
    cA
    cC
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    cc
    cubic.m
    wph
    @33
    @35
    wph
    cB
    cubic.b
    sqcld
    wph
    c3
    cc
    wcel
    @34
    cc
    wcel
    @35
    cc
    wcel
    3cn
    wph
    cA
    cC
    cubic.a
    cubic.c
    mulcld
    c3
    @34
    mulcl
    sylancr
    subcld
    eqeltrd
    #
    3nn0
    cM
    c3
    expcl
    sylancl
    #
    c4
    @27
    mulcl
    sylancr
    #
    subcld
    eqeltrd
    #
    sqrtcld
    #
    addcld
    #
    halfcld
    #
    c3
    3cn
    3ne0
    reccli
    #
    @7
    @8
    cxpcl
    sylancl
    eqeltrd
    wph
    cT
    c3
    cexp
    co
    @9
    c3
    cexp
    co
    #
    @7
    wph
    cT
    @9
    c3
    cexp
    cubic.t
    oveq1d
    wph
    @10
    c3
    cn
    wcel
    @44
    @7
    wceq
    @42
    3nn
    @7
    c3
    cxproot
    sylancl
    eqtrd
    @40
    wph
    @5
    c2
    cexp
    co
    #
    cG
    @29
    wph
    cG
    @39
    sqsqrtd
    cubic.g
    eqtrd
    #
    cubic.m
    cubic.n
    wph
    cT
    @9
    cc0
    cubic.t
    wph
    @7
    @8
    @42
    wph
    @6
    c2
    @41
    @22
    wph
    2cn
    a1i
    wph
    @6
    cN
    @5
    cmin
    co
    #
    cmul
    co
    #
    cc0
    @47
    cmul
    co
    #
    wne
    @6
    cc0
    wne
    wph
    @28
    cc0
    @48
    @49
    wph
    c4
    @27
    @31
    wph
    4cn
    a1i
    @37
    c4
    cc0
    wne
    wph
    4ne0
    a1i
    wph
    cM
    c3
    @36
    cubic.0
    c3
    cz
    wcel
    wph
    3z
    a1i
    expne0d
    mulne0d
    wph
    @26
    @45
    cmin
    co
    #
    @26
    @29
    cmin
    co
    @48
    @28
    wph
    @45
    @29
    @26
    cmin
    @46
    oveq2d
    wph
    cN
    cc
    wcel
    @5
    cc
    wcel
    @50
    @48
    wceq
    @25
    @40
    cN
    @5
    subsq
    syl2anc
    wph
    @26
    @28
    @30
    @38
    nncand
    3eqtr3d
    wph
    @47
    wph
    cN
    @5
    @25
    @40
    subcld
    mul02d
    3netr4d
    @6
    cc0
    @48
    @49
    @6
    cc0
    @47
    cmul
    oveq1
    necon3i
    syl
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divne0d
    @11
    wph
    @43
    a1i
    cxpne0d
    eqnetrd
    cubic2
    @3
    @4
    vr
    cR
    cc
    @0
    cR
    wcel
    #
    @3
    wa
    @0
    cc
    wcel
    #
    @1
    wa
    #
    @3
    wa
    @52
    @4
    wa
    @51
    @53
    @3
    @0
    cR
    cubic.r
    1cubr
    anbi1i
    @52
    @1
    @3
    anass
    bitri
    rexbii2
    syl6bbr
end
