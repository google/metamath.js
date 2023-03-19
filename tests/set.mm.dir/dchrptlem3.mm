include "cv.mm"
include "cdpj.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "cdm.mm"
include "wrex.mm"
include "c1.mm"
include "wne.mm"
include "wral.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c0g.mm"
include "cmnd.mm"
include "wcel.mm"
include "cvv.mm"
include "cgrp.mm"
include "crg.mm"
include "ccrg.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "syl.mm"
include "crngring.mm"
include "unitgrp.mm"
include "grpmnd.mm"
include "cword.mm"
include "dmexg.mm"
include "eqid.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "unitgrpid.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "neeqtrrd.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cixp.mm"
include "crab.mm"
include "cz.mm"
include "crn.mm"
include "zex.mm"
include "mptex.mm"
include "rnex.mm"
include "dmmpti.mm"
include "a1i.mm"
include "cdprd.mm"
include "eleqtrrd.mm"
include "wa.mm"
include "adantr.mm"
include "csubg.mm"
include "dprdf2.mm"
include "ffvelrnda.mm"
include "subg0cl.mm"
include "eqeltrd.mm"
include "csn.mm"
include "cxp.mm"
include "cur.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fczfsuppd.mm"
include "fconstmpt.mm"
include "eqcomi.mm"
include "eqcomd.mm"
include "3brtr4d.mm"
include "dprdwd.mm"
include "dpjeq.mm"
include "necon3abid.mm"
include "mpbid.mm"
include "rexnal.mm"
include "sylibr.mm"
include "df-ne.mm"
include "cneg.mm"
include "c2.mm"
include "cod.mm"
include "cdiv.mm"
include "ccxp.mm"
include "cexp.mm"
include "cio.mm"
include "cn.mm"
include "simprl.mm"
include "simprr.mm"
include "dchrptlem2.mm"
include "expr.mm"
include "syl5bir.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem dchrptlem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cN: class N
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cI: class I
  let vy: setvar y
  let cC: class C
  let vi: setvar i
  let cX: class X
  let cP: class P
  let cM: class M
  let cT: class T
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

  disjoint k n
  disjoint k x
  disjoint .1. k
  disjoint n x
  disjoint .1. n
  disjoint .1. x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B x
  disjoint G x
  disjoint H k
  disjoint H n
  disjoint H x
  disjoint N x
  disjoint W k
  disjoint W n
  disjoint W x
  disjoint .x. k
  disjoint .x. n
  disjoint .x. x
  disjoint S k
  disjoint S n
  disjoint S x
  disjoint Z k
  disjoint Z n
  disjoint Z x
  disjoint D x
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint U x
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
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h x
  disjoint .1. h
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint .1. m
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint A a
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint A b
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint A h
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint A m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint I a
  disjoint I b
  disjoint I h
  disjoint I k
  disjoint I m
  disjoint I u
  disjoint I v
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B y
  disjoint C h
  disjoint C m
  disjoint C u
  disjoint a i
  disjoint H a
  disjoint h i
  disjoint H h
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i x
  disjoint H i
  disjoint H m
  disjoint H u
  disjoint W a
  disjoint b i
  disjoint W b
  disjoint W h
  disjoint i v
  disjoint W i
  disjoint W m
  disjoint W u
  disjoint W v
  disjoint .x. a
  disjoint .x. b
  disjoint .x. h
  disjoint .x. m
  disjoint .x. u
  disjoint .x. v
  disjoint a y
  disjoint X a
  disjoint b y
  disjoint X b
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint P a
  disjoint P b
  disjoint P h
  disjoint P m
  disjoint P u
  disjoint P v
  disjoint S a
  disjoint S h
  disjoint S i
  disjoint S m
  disjoint S u
  disjoint Z a
  disjoint Z b
  disjoint h y
  disjoint Z h
  disjoint k y
  disjoint m y
  disjoint Z m
  disjoint n y
  disjoint u y
  disjoint Z u
  disjoint Z v
  disjoint w y
  disjoint Z w
  disjoint Z y
  disjoint D a
  disjoint D w
  disjoint M h
  disjoint M m
  disjoint a ph
  disjoint b ph
  disjoint h ph
  disjoint i w
  disjoint i y
  disjoint i ph
  disjoint m ph
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint T h
  disjoint T m
  disjoint T u
  disjoint U a
  disjoint U b
  disjoint U h
  disjoint U m
  disjoint U u
  disjoint U v
  disjoint U y
  assert |- ( ph -> E. x e. D ( x ` A ) =/= 1 )

  proof
    wph
    cA
    va
    cv
    #
    cH
    cS
    cdpj
    co
    #
    cfv
    #
    cfv
    #
    c.1
    wceq
    #
    wn
    #
    va
    cW
    cdm
    #
    wrex
    #
    cA
    vx
    cv
    cfv
    c1
    wne
    vx
    cD
    wrex
    #
    wph
    @4
    va
    @6
    wral
    #
    wn
    #
    @7
    wph
    cA
    cH
    va
    @6
    c.1
    cmpt
    #
    cgsu
    co
    #
    wne
    @10
    wph
    cA
    c.1
    @12
    dchrpt.n1
    wph
    cH
    va
    @6
    cH
    c0g
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @13
    @12
    c.1
    wph
    cH
    cmnd
    wcel
    #
    @6
    cvv
    wcel
    #
    @15
    @13
    wceq
    wph
    cH
    cgrp
    wcel
    #
    @16
    wph
    cZ
    crg
    wcel
    #
    @18
    wph
    cZ
    ccrg
    wcel
    #
    @19
    wph
    cN
    cn0
    wcel
    @20
    wph
    cN
    dchrpt.n
    nnnn0d
    cN
    cZ
    dchrpt.z
    zncrng
    syl
    cZ
    crngring
    syl
    #
    cZ
    cU
    cH
    dchrpt.u
    dchrpt.h
    unitgrp
    syl
    cH
    grpmnd
    syl
    wph
    cW
    cU
    cword
    #
    wcel
    #
    @17
    dchrpt.w
    cW
    @22
    dmexg
    syl
    #
    @6
    va
    cH
    cvv
    @13
    @13
    eqid
    #
    gsumz
    syl2anc
    wph
    @11
    @14
    cH
    cgsu
    wph
    va
    @6
    c.1
    @13
    wph
    @19
    c.1
    @13
    wceq
    #
    @21
    cZ
    cU
    c.1
    cH
    dchrpt.u
    dchrpt.h
    dchrpt.1
    unitgrpid
    syl
    #
    mpteq2dv
    oveq2d
    @27
    3eqtr4d
    neeqtrrd
    wph
    @9
    cA
    @12
    wph
    va
    cA
    c.1
    @1
    cS
    vh
    vi
    cH
    @6
    vh
    cv
    #
    @13
    cfsupp
    wbr
    vh
    vi
    @6
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    @13
    dchrpt.2
    cS
    cdm
    @6
    wceq
    wph
    vk
    @6
    vn
    cz
    vn
    cv
    vk
    cv
    cW
    cfv
    c.x
    co
    #
    cmpt
    #
    crn
    cS
    @31
    vn
    cz
    @30
    zex
    mptex
    rnex
    dchrpt.s
    dmmpti
    a1i
    #
    @1
    eqid
    #
    wph
    cA
    cU
    cH
    cS
    cdprd
    co
    #
    dchrpt.au
    dchrpt.3
    eleqtrrd
    @25
    @29
    eqid
    #
    wph
    va
    c.1
    cS
    vh
    vi
    cH
    @6
    @29
    @13
    @35
    dchrpt.2
    @32
    wph
    @0
    @6
    wcel
    #
    wa
    #
    c.1
    @13
    @0
    cS
    cfv
    #
    wph
    @26
    @36
    @27
    adantr
    @37
    @38
    cH
    csubg
    cfv
    #
    wcel
    @13
    @38
    wcel
    wph
    @6
    @39
    @0
    cS
    wph
    cS
    cH
    @6
    dchrpt.2
    @32
    dprdf2
    ffvelrnda
    @38
    cH
    @13
    @25
    subg0cl
    syl
    eqeltrd
    wph
    @6
    c.1
    csn
    cxp
    #
    c.1
    @11
    @13
    cfsupp
    wph
    @6
    cvv
    cvv
    c.1
    @24
    c.1
    cvv
    wcel
    wph
    c.1
    cZ
    cur
    cfv
    cvv
    dchrpt.1
    cZ
    cur
    fvex
    eqeltri
    a1i
    fczfsuppd
    @11
    @40
    wceq
    wph
    @40
    @11
    va
    @6
    c.1
    fconstmpt
    eqcomi
    a1i
    wph
    c.1
    @13
    @27
    eqcomd
    3brtr4d
    dprdwd
    dpjeq
    necon3abid
    mpbid
    @4
    va
    @6
    rexnal
    sylibr
    wph
    @5
    @8
    va
    @6
    @5
    @3
    c.1
    wne
    #
    @37
    @8
    @3
    c.1
    df-ne
    wph
    @36
    @41
    @8
    wph
    @36
    @41
    wa
    #
    wa
    vx
    vu
    cA
    cB
    cD
    @1
    cS
    c1
    cneg
    c2
    @0
    cW
    cfv
    #
    cH
    cod
    cfv
    #
    cfv
    cdiv
    co
    ccxp
    co
    #
    c.x
    cU
    c.1
    vh
    vk
    vm
    vn
    cG
    cH
    @0
    cN
    @44
    cW
    vu
    cU
    vu
    cv
    @2
    cfv
    vm
    cv
    #
    @43
    c.x
    co
    wceq
    @28
    @45
    @46
    cexp
    co
    wceq
    wa
    vm
    cz
    wrex
    vh
    cio
    cmpt
    #
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    dchrpt.1
    wph
    cN
    cn
    wcel
    @42
    dchrpt.n
    adantr
    wph
    cA
    c.1
    wne
    @42
    dchrpt.n1
    adantr
    dchrpt.u
    dchrpt.h
    dchrpt.m
    dchrpt.s
    wph
    cA
    cU
    wcel
    @42
    dchrpt.au
    adantr
    wph
    @23
    @42
    dchrpt.w
    adantr
    wph
    cH
    cS
    cdprd
    cdm
    wbr
    @42
    dchrpt.2
    adantr
    wph
    @34
    cU
    wceq
    @42
    dchrpt.3
    adantr
    @33
    @44
    eqid
    @45
    eqid
    wph
    @36
    @41
    simprl
    wph
    @36
    @41
    simprr
    @47
    eqid
    dchrptlem2
    expr
    syl5bir
    rexlimdva
    mpd
end
