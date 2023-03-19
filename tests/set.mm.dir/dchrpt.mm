include "cui.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "wne.mm"
include "wrex.mm"
include "wa.mm"
include "cdm.mm"
include "cmgp.mm"
include "cress.mm"
include "co.mm"
include "ccyg.mm"
include "cpgp.mm"
include "crn.mm"
include "cin.mm"
include "csubg.mm"
include "crab.mm"
include "cz.mm"
include "cmg.mm"
include "cmpt.mm"
include "wf.mm"
include "cdprd.mm"
include "wbr.mm"
include "wceq.mm"
include "w3a.mm"
include "cword.mm"
include "cn.mm"
include "ad3antrrr.mm"
include "eqid.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "dchrptlem3.mm"
include "3adantr1.mm"
include "unitgrpbas.mm"
include "cabl.mm"
include "cn0.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "unitabl.mm"
include "3syl.mm"
include "adantr.mm"
include "cfn.mm"
include "wss.mm"
include "znfi.mm"
include "syl.mm"
include "unitss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "ablfac2.mm"
include "r19.29a.mm"
include "wn.mm"
include "c0g.mm"
include "cgrp.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "grpidcl.mm"
include "4syl.mm"
include "cc0.mm"
include "0ne1.mm"
include "dchrn0.mm"
include "necon1bbid.mm"
include "biimpa.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "fveq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"

theorem dchrpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let c.1: class .1.
  let cG: class G
  let cN: class N
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cI: class I
  let vy: setvar y
  let cC: class C
  let vi: setvar i
  let cH: class H
  let cW: class W
  let c.x: class .x.
  let cX: class X
  let cP: class P
  let cS: class S
  let cM: class M
  let cT: class T
  let cU: class U
  assume dchrpt.g: |- G = ( DChr ` N )
  assume dchrpt.z: |- Z = ( Z/nZ ` N )
  assume dchrpt.d: |- D = ( Base ` G )
  assume dchrpt.b: |- B = ( Base ` Z )
  assume dchrpt.1: |- .1. = ( 1r ` Z )
  assume dchrpt.n: |- ( ph -> N e. NN )
  assume dchrpt.n1: |- ( ph -> A =/= .1. )
  assume dchrpt.a: |- ( ph -> A e. B )

  disjoint .1. x
  disjoint A x
  disjoint B x
  disjoint G x
  disjoint N x
  disjoint Z x
  disjoint D x
  disjoint ph x
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
  disjoint k n
  disjoint k x
  disjoint .1. k
  disjoint m n
  disjoint m x
  disjoint .1. m
  disjoint n x
  disjoint .1. n
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
  disjoint A k
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint A m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint A n
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
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H u
  disjoint H x
  disjoint W a
  disjoint b i
  disjoint W b
  disjoint W h
  disjoint i v
  disjoint W i
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W u
  disjoint W v
  disjoint W x
  disjoint .x. a
  disjoint .x. b
  disjoint .x. h
  disjoint .x. k
  disjoint .x. m
  disjoint .x. n
  disjoint .x. u
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
  disjoint P h
  disjoint P m
  disjoint P u
  disjoint P v
  disjoint S a
  disjoint S h
  disjoint S i
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S x
  disjoint Z a
  disjoint Z b
  disjoint h y
  disjoint Z h
  disjoint k y
  disjoint Z k
  disjoint m y
  disjoint Z m
  disjoint n y
  disjoint Z n
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
  disjoint k ph
  disjoint m ph
  disjoint n ph
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
  disjoint U x
  disjoint U y
  assert |- ( ph -> E. x e. D ( x ` A ) =/= 1 )

  proof
    wph
    cA
    cZ
    cui
    cfv
    #
    wcel
    #
    cA
    vx
    cv
    #
    cfv
    #
    c1
    wne
    #
    vx
    cD
    wrex
    #
    wph
    @1
    wa
    #
    vw
    cv
    #
    cdm
    #
    cZ
    cmgp
    cfv
    @0
    cress
    co
    #
    vu
    cv
    cress
    co
    ccyg
    cpgp
    crn
    cin
    wcel
    vu
    @9
    csubg
    cfv
    crab
    #
    vk
    @8
    vn
    cz
    vn
    cv
    #
    vk
    cv
    #
    @7
    cfv
    #
    @9
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cmpt
    #
    wf
    #
    @9
    @18
    cdprd
    cdm
    wbr
    #
    @9
    @18
    cdprd
    co
    @0
    wceq
    #
    w3a
    @5
    vw
    @0
    cword
    #
    @6
    @7
    @22
    wcel
    #
    wa
    #
    @20
    @21
    @5
    @19
    @24
    @20
    @21
    wa
    #
    wa
    vx
    cA
    cB
    cD
    @18
    @14
    @0
    c.1
    va
    vb
    cG
    @9
    cN
    @7
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
    #
    @1
    @23
    @25
    dchrpt.n
    ad3antrrr
    wph
    cA
    c.1
    wne
    @1
    @23
    @25
    dchrpt.n1
    ad3antrrr
    @0
    eqid
    #
    @9
    eqid
    #
    @14
    eqid
    #
    vk
    va
    @8
    @17
    vb
    cz
    vb
    cv
    #
    va
    cv
    #
    @7
    cfv
    #
    @14
    co
    #
    cmpt
    #
    crn
    @12
    @31
    wceq
    #
    @16
    @34
    @35
    @16
    vb
    cz
    @30
    @13
    @14
    co
    #
    cmpt
    @34
    vn
    vb
    cz
    @15
    @36
    @11
    @30
    @13
    @14
    oveq1
    cbvmptv
    @35
    vb
    cz
    @36
    @33
    @35
    @13
    @32
    @30
    @14
    @12
    @31
    @7
    fveq2
    oveq2d
    mpteq2dv
    syl5eq
    rneqd
    cbvmptv
    wph
    @1
    @23
    @25
    simpllr
    @6
    @23
    @25
    simplr
    @24
    @20
    @21
    simprl
    @24
    @20
    @21
    simprr
    dchrptlem3
    3adantr1
    @6
    vw
    @0
    @10
    @18
    @14
    vk
    vn
    @9
    vu
    cZ
    @0
    @9
    @27
    @28
    unitgrpbas
    @10
    eqid
    wph
    @9
    cabl
    wcel
    #
    @1
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    @37
    wph
    cN
    dchrpt.n
    nnnn0d
    cN
    cZ
    dchrpt.z
    zncrng
    cZ
    @0
    @9
    @27
    @28
    unitabl
    3syl
    adantr
    wph
    @0
    cfn
    wcel
    #
    @1
    wph
    cB
    cfn
    wcel
    #
    @0
    cB
    wss
    @38
    wph
    @26
    @39
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
    @0
    dchrpt.b
    @27
    unitss
    cB
    @0
    ssfi
    sylancl
    adantr
    @29
    @18
    eqid
    ablfac2
    r19.29a
    wph
    @1
    wn
    #
    wa
    #
    cG
    c0g
    cfv
    #
    cD
    wcel
    #
    cA
    @42
    cfv
    #
    c1
    wne
    #
    @5
    wph
    @43
    @40
    wph
    @26
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    @43
    dchrpt.n
    cG
    cN
    dchrpt.g
    dchrabl
    cG
    ablgrp
    cD
    cG
    @42
    dchrpt.d
    @42
    eqid
    grpidcl
    4syl
    #
    adantr
    @41
    @45
    cc0
    c1
    wne
    0ne1
    @41
    @44
    cc0
    c1
    wph
    @40
    @44
    cc0
    wceq
    wph
    @1
    @44
    cc0
    wph
    cA
    cB
    cD
    @0
    cG
    cN
    @42
    cZ
    dchrpt.g
    dchrpt.z
    dchrpt.d
    dchrpt.b
    @27
    @46
    dchrpt.a
    dchrn0
    necon1bbid
    biimpa
    neeq1d
    mpbiri
    @4
    @45
    vx
    @42
    cD
    @2
    @42
    wceq
    @3
    @44
    c1
    cA
    @2
    @42
    fveq1
    neeq1d
    rspcev
    syl2anc
    pm2.61dan
end
