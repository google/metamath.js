include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cexp.mm"
include "wrex.mm"
include "cio.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "iotabidv.mm"
include "iotaex.mm"
include "fvmpt3i.mm"
include "ad2antlr.mm"
include "cvv.mm"
include "ovex.mm"
include "wb.mm"
include "simpr.mm"
include "simpllr.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "wi.mm"
include "simp-4l.mm"
include "simplr.mm"
include "simpld.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cgrp.mm"
include "cn0.mm"
include "ccrg.mm"
include "crg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "unitgrp.mm"
include "4syl.mm"
include "adantr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "cword.mm"
include "wf.mm"
include "wrdf.mm"
include "syl.mm"
include "cdm.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "simprl.mm"
include "simprr.mm"
include "c0g.mm"
include "unitgrpbas.mm"
include "eqid.mm"
include "odcong.mm"
include "syl112anc.mm"
include "caddc.mm"
include "cmul.mm"
include "cc.mm"
include "wne.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cdiv.mm"
include "ccxp.mm"
include "neg1cn.mm"
include "cr.mm"
include "cn.mm"
include "2re.mm"
include "cfn.mm"
include "wss.mm"
include "znfi.mm"
include "unitss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "odcl2.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "nndivre.mm"
include "sylancr.mm"
include "recnd.mm"
include "cxpcl.mm"
include "syl5eqel.mm"
include "a1i.mm"
include "neg1ne0.mm"
include "cxpne0d.mm"
include "neeq1i.mm"
include "sylibr.mm"
include "zsubcl.mm"
include "expaddz.mm"
include "syl22anc.mm"
include "zcnd.mm"
include "npcand.mm"
include "oveq2d.mm"
include "oveq1i.mm"
include "root1eq1.mm"
include "syl2an.mm"
include "biimpar.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "expclzd.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "sylbird.mm"
include "syl12anc.mm"
include "mpd.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "oveq1.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "expr.mm"
include "adantl.mm"
include "impbid.mm"
include "iota5.mm"
include "mpan2.mm"

theorem dchrptlem1
  let wph: wff ph
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vi: setvar i
  assume dchrpt.g: |- G = ( DChr ` N )
  assume dchrpt.z: |- Z = ( Z/nZ ` N )
  assume dchrpt.d: |- D = ( Base ` G )
  assume dchrpt.b: |- B = ( Base ` Z )
  assume dchrpt.1: |- .1. = ( 1r ` Z )
  assume dchrpt.n: |- ( ph -> N e. NN )
  assume dchrpt.n1: |- ( ph -> A =/= .1. )
  assume dchrpt.u: |- U = ( Unit ` Z )
  assume dchrpt.h: |- H = ( ( mulGrp ` Z ) |`s U )
  assume dchrpt.m: |- .x. = ( .g ` H )
  assume dchrpt.s: |- S = ( k e. dom W |-> ran ( n e. ZZ |-> ( n .x. ( W ` k ) ) ) )
  assume dchrpt.au: |- ( ph -> A e. U )
  assume dchrpt.w: |- ( ph -> W e. Word U )
  assume dchrpt.2: |- ( ph -> H dom DProd S )
  assume dchrpt.3: |- ( ph -> ( H DProd S ) = U )
  assume dchrpt.p: |- P = ( H dProj S )
  assume dchrpt.o: |- O = ( od ` H )
  assume dchrpt.t: |- T = ( -u 1 ^c ( 2 / ( O ` ( W ` I ) ) ) )
  assume dchrpt.i: |- ( ph -> I e. dom W )
  assume dchrpt.4: |- ( ph -> ( ( P ` I ) ` A ) =/= .1. )
  assume dchrpt.5: |- X = ( u e. U |-> ( iota h E. m e. ZZ ( ( ( P ` I ) ` u ) = ( m .x. ( W ` I ) ) /\ h = ( T ^ m ) ) ) )

  disjoint h k
  disjoint h m
  disjoint h n
  disjoint .1. h
  disjoint k m
  disjoint k n
  disjoint .1. k
  disjoint m n
  disjoint .1. m
  disjoint .1. n
  disjoint h u
  disjoint A h
  disjoint k u
  disjoint A k
  disjoint m u
  disjoint A m
  disjoint n u
  disjoint A n
  disjoint A u
  disjoint I h
  disjoint I k
  disjoint I m
  disjoint I u
  disjoint C h
  disjoint C m
  disjoint C u
  disjoint H h
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H u
  disjoint W h
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W u
  disjoint .x. h
  disjoint .x. k
  disjoint .x. m
  disjoint .x. n
  disjoint .x. u
  disjoint P h
  disjoint P m
  disjoint P u
  disjoint S h
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint Z h
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z u
  disjoint M h
  disjoint M m
  disjoint h ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint T h
  disjoint T m
  disjoint T u
  disjoint U h
  disjoint U m
  disjoint U u
  disjoint a b
  disjoint a h
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint .1. a
  disjoint b h
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint .1. b
  disjoint h x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint .1. x
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint A a
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint A b
  disjoint h v
  disjoint h w
  disjoint k v
  disjoint k w
  disjoint m v
  disjoint m w
  disjoint n v
  disjoint n w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint I a
  disjoint I b
  disjoint I v
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint a i
  disjoint H a
  disjoint h i
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i x
  disjoint H i
  disjoint H x
  disjoint N x
  disjoint W a
  disjoint b i
  disjoint W b
  disjoint i v
  disjoint W i
  disjoint W v
  disjoint W x
  disjoint .x. a
  disjoint .x. b
  disjoint .x. v
  disjoint .x. x
  disjoint a y
  disjoint X a
  disjoint b y
  disjoint X b
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint P a
  disjoint P b
  disjoint P v
  disjoint S a
  disjoint S i
  disjoint S x
  disjoint Z a
  disjoint Z b
  disjoint h y
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint u y
  disjoint Z v
  disjoint w y
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint D a
  disjoint D w
  disjoint D x
  disjoint a ph
  disjoint b ph
  disjoint i w
  disjoint i y
  disjoint i ph
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint U a
  disjoint U b
  disjoint U v
  disjoint U x
  disjoint U y
  assert |- ( ( ( ph /\ C e. U ) /\ ( M e. ZZ /\ ( ( P ` I ) ` C ) = ( M .x. ( W ` I ) ) ) ) -> ( X ` C ) = ( T ^ M ) )

  proof
    wph
    cC
    cU
    wcel
    #
    wa
    #
    cM
    cz
    wcel
    #
    cC
    cI
    cP
    cfv
    #
    cfv
    #
    cM
    cI
    cW
    cfv
    #
    c.x
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    cC
    cX
    cfv
    #
    @4
    vm
    cv
    #
    @5
    c.x
    co
    #
    wceq
    #
    vh
    cv
    #
    cT
    @11
    cexp
    co
    #
    wceq
    #
    wa
    #
    vm
    cz
    wrex
    #
    vh
    cio
    #
    cT
    cM
    cexp
    co
    #
    @0
    @10
    @19
    wceq
    wph
    @8
    vu
    cC
    vu
    cv
    #
    @3
    cfv
    #
    @12
    wceq
    #
    @16
    wa
    #
    vm
    cz
    wrex
    #
    vh
    cio
    @19
    cU
    cX
    @21
    cC
    wceq
    #
    @25
    @18
    vh
    @26
    @24
    @17
    vm
    cz
    @26
    @23
    @13
    @16
    @26
    @22
    @4
    @12
    @21
    cC
    @3
    fveq2
    eqeq1d
    anbi1d
    rexbidv
    iotabidv
    dchrpt.5
    @25
    vh
    iotaex
    fvmpt3i
    ad2antlr
    @9
    @20
    cvv
    wcel
    #
    @19
    @20
    wceq
    cT
    cM
    cexp
    ovex
    @9
    @18
    vh
    @20
    cvv
    @9
    @18
    @14
    @20
    wceq
    #
    wb
    @27
    @9
    @18
    @28
    @9
    @17
    @28
    vm
    cz
    @9
    @11
    cz
    wcel
    #
    wa
    #
    @13
    @16
    @28
    @30
    @13
    wa
    #
    @16
    @28
    @31
    @15
    @20
    @14
    @31
    @12
    @6
    wceq
    #
    @15
    @20
    wceq
    #
    @31
    @4
    @12
    @6
    @30
    @13
    simpr
    @31
    @2
    @7
    @1
    @8
    @29
    @13
    simpllr
    #
    simprd
    eqtr3d
    @31
    wph
    @29
    @2
    @32
    @33
    wi
    wph
    @0
    @8
    @29
    @13
    simp-4l
    @9
    @29
    @13
    simplr
    @31
    @2
    @7
    @34
    simpld
    wph
    @29
    @2
    wa
    #
    wa
    #
    @32
    @5
    cO
    cfv
    #
    @11
    cM
    cmin
    co
    #
    cdvds
    wbr
    #
    @33
    @36
    cH
    cgrp
    wcel
    #
    @5
    cU
    wcel
    #
    @29
    @2
    @39
    @32
    wb
    wph
    @40
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
    @40
    wph
    cN
    dchrpt.n
    nnnn0d
    cN
    cZ
    dchrpt.z
    zncrng
    cZ
    crngring
    cZ
    cU
    cH
    dchrpt.u
    dchrpt.h
    unitgrp
    4syl
    #
    adantr
    wph
    @41
    @35
    wph
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    cU
    cI
    cW
    wph
    cW
    cU
    cword
    wcel
    @43
    cU
    cW
    wf
    #
    dchrpt.w
    cU
    cW
    wrdf
    syl
    #
    wph
    cI
    cW
    cdm
    #
    @43
    dchrpt.i
    wph
    @44
    @46
    @43
    wceq
    @45
    @43
    cU
    cW
    fdm
    syl
    eleqtrd
    ffvelrnd
    #
    adantr
    wph
    @29
    @2
    simprl
    #
    wph
    @29
    @2
    simprr
    #
    @5
    c.x
    cH
    @11
    cM
    cO
    cU
    cH
    c0g
    cfv
    #
    cZ
    cU
    cH
    dchrpt.u
    dchrpt.h
    unitgrpbas
    #
    dchrpt.o
    dchrpt.m
    @50
    eqid
    odcong
    syl112anc
    @36
    @39
    @33
    @36
    @39
    wa
    #
    cT
    @38
    cM
    caddc
    co
    #
    cexp
    co
    #
    cT
    @38
    cexp
    co
    #
    @20
    cmul
    co
    #
    @15
    @20
    @52
    cT
    cc
    wcel
    cT
    cc0
    wne
    #
    @38
    cz
    wcel
    #
    @2
    @54
    @56
    wceq
    @52
    cT
    c1
    cneg
    #
    c2
    @37
    cdiv
    co
    #
    ccxp
    co
    #
    cc
    dchrpt.t
    @52
    @59
    cc
    wcel
    #
    @60
    cc
    wcel
    @61
    cc
    wcel
    neg1cn
    @52
    @60
    @52
    c2
    cr
    wcel
    @37
    cn
    wcel
    #
    @60
    cr
    wcel
    2re
    wph
    @63
    @35
    @39
    wph
    @40
    cU
    cfn
    wcel
    #
    @41
    @63
    @42
    wph
    cB
    cfn
    wcel
    #
    cU
    cB
    wss
    @64
    wph
    cN
    cn
    wcel
    @65
    dchrpt.n
    cB
    cN
    cZ
    dchrpt.z
    dchrpt.b
    znfi
    syl
    cB
    cZ
    cU
    dchrpt.b
    dchrpt.u
    unitss
    cB
    cU
    ssfi
    sylancl
    @47
    @5
    cH
    cO
    cU
    @51
    dchrpt.o
    odcl2
    syl3anc
    #
    ad2antrr
    c2
    @37
    nndivre
    sylancr
    recnd
    #
    @59
    @60
    cxpcl
    sylancr
    syl5eqel
    #
    @52
    @61
    cc0
    wne
    @57
    @52
    @59
    @60
    @62
    @52
    neg1cn
    a1i
    @59
    cc0
    wne
    @52
    neg1ne0
    a1i
    @67
    cxpne0d
    cT
    @61
    cc0
    dchrpt.t
    neeq1i
    sylibr
    #
    @35
    @58
    wph
    @39
    @11
    cM
    zsubcl
    #
    ad2antlr
    @36
    @2
    @39
    @49
    adantr
    #
    cT
    @38
    cM
    expaddz
    syl22anc
    @52
    @53
    @11
    cT
    cexp
    @52
    @11
    cM
    @52
    @11
    @36
    @29
    @39
    @48
    adantr
    zcnd
    @52
    cM
    @71
    zcnd
    npcand
    oveq2d
    @52
    @56
    c1
    @20
    cmul
    co
    @20
    @52
    @55
    c1
    @20
    cmul
    @52
    @55
    @61
    @38
    cexp
    co
    #
    c1
    cT
    @61
    @38
    cexp
    dchrpt.t
    oveq1i
    @36
    @72
    c1
    wceq
    #
    @39
    wph
    @63
    @58
    @73
    @39
    wb
    @35
    @66
    @70
    @38
    @37
    root1eq1
    syl2an
    biimpar
    syl5eq
    oveq1d
    @52
    @20
    @52
    cT
    cM
    @68
    @69
    @71
    expclzd
    mulid2d
    eqtrd
    3eqtr3d
    ex
    sylbird
    syl12anc
    mpd
    eqeq2d
    biimpd
    expimpd
    rexlimdva
    @8
    @28
    @18
    wi
    @1
    @2
    @7
    @28
    @18
    @17
    @7
    @28
    wa
    vm
    cM
    cz
    @11
    cM
    wceq
    #
    @13
    @7
    @16
    @28
    @74
    @12
    @6
    @4
    @11
    cM
    @5
    c.x
    oveq1
    eqeq2d
    @74
    @15
    @20
    @14
    @11
    cM
    cT
    cexp
    oveq2
    eqeq2d
    anbi12d
    rspcev
    expr
    adantl
    impbid
    adantr
    iota5
    mpan2
    eqtrd
end
