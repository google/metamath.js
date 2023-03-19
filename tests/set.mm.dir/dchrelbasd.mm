include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cc.mm"
include "wf.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "cur.mm"
include "c1.mm"
include "wne.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "adantlr.mm"
include "wn.mm"
include "0cnd.mm"
include "ifclda.mm"
include "eqid.mm"
include "fmptd.mm"
include "crg.mm"
include "cn0.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "3syl.mm"
include "unitmulcl.mm"
include "3expb.mm"
include "sylan.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "unitss.mm"
include "sseldi.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "simprl.mm"
include "iftrue.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "1unit.mm"
include "syl.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "simpr.mm"
include "mpan9.mm"
include "neeq1d.mm"
include "iffalse.mm"
include "necon1ai.mm"
include "syl6bi.mm"
include "3jca.mm"
include "dchrelbas3.mm"
include "mpbir2and.mm"

theorem dchrelbasd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vz: setvar z
  let vb: setvar b
  let vn: setvar n
  assume dchrval.g: |- G = ( DChr ` N )
  assume dchrval.z: |- Z = ( Z/nZ ` N )
  assume dchrval.b: |- B = ( Base ` Z )
  assume dchrval.u: |- U = ( Unit ` Z )
  assume dchrval.n: |- ( ph -> N e. NN )
  assume dchrbas.b: |- D = ( Base ` G )
  assume dchrelbasd.1: |- ( k = x -> X = A )
  assume dchrelbasd.2: |- ( k = y -> X = C )
  assume dchrelbasd.3: |- ( k = ( x ( .r ` Z ) y ) -> X = E )
  assume dchrelbasd.4: |- ( k = ( 1r ` Z ) -> X = Y )
  assume dchrelbasd.5: |- ( ( ph /\ k e. U ) -> X e. CC )
  assume dchrelbasd.6: |- ( ( ph /\ ( x e. U /\ y e. U ) ) -> E = ( A x. C ) )
  assume dchrelbasd.7: |- ( ph -> Y = 1 )

  disjoint A k
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint N x
  disjoint U k
  disjoint U x
  disjoint U y
  disjoint C k
  disjoint E k
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Z k
  disjoint Z x
  disjoint Z y
  disjoint Y k
  disjoint k z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint b n
  disjoint b z
  disjoint D b
  disjoint n z
  disjoint D n
  disjoint D z
  disjoint b x
  disjoint N b
  disjoint n x
  disjoint N n
  disjoint N z
  disjoint U z
  disjoint b k
  disjoint b y
  disjoint b ph
  disjoint k n
  disjoint n y
  disjoint n ph
  disjoint ph z
  disjoint X z
  disjoint Z z
  assert |- ( ph -> ( k e. B |-> if ( k e. U , X , 0 ) ) e. D )

  proof
    wph
    vk
    cB
    vk
    cv
    #
    cU
    wcel
    #
    cX
    cc0
    cif
    #
    cmpt
    #
    cD
    wcel
    cB
    cc
    @3
    wf
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
    @3
    cfv
    #
    @4
    @3
    cfv
    #
    @5
    @3
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cU
    wral
    vx
    cU
    wral
    #
    cZ
    cur
    cfv
    #
    @3
    cfv
    #
    c1
    wceq
    #
    @9
    cc0
    wne
    #
    @4
    cU
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    w3a
    wph
    vk
    cB
    @2
    cc
    @3
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @1
    cX
    cc0
    cc
    wph
    @1
    cX
    cc
    wcel
    #
    @21
    dchrelbasd.5
    adantlr
    @22
    @1
    wn
    wa
    0cnd
    ifclda
    @3
    eqid
    #
    fmptd
    wph
    @13
    @16
    @20
    wph
    @12
    vx
    vy
    cU
    cU
    wph
    @18
    @5
    cU
    wcel
    #
    wa
    #
    wa
    #
    @7
    cU
    wcel
    #
    cE
    cc0
    cif
    #
    cA
    cC
    cmul
    co
    #
    @8
    @11
    @27
    @29
    cE
    @30
    @27
    @28
    cE
    cc0
    wph
    cZ
    crg
    wcel
    #
    @26
    @28
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    @31
    wph
    cN
    dchrval.n
    nnnn0d
    cN
    cZ
    dchrval.z
    zncrng
    cZ
    crngring
    3syl
    #
    @31
    @18
    @25
    @28
    cZ
    @6
    cU
    @4
    @5
    dchrval.u
    @6
    eqid
    unitmulcl
    3expb
    sylan
    #
    iftrued
    #
    dchrelbasd.6
    eqtrd
    @27
    @7
    cB
    wcel
    @29
    cc
    wcel
    @8
    @29
    wceq
    @27
    cU
    cB
    @7
    cB
    cZ
    cU
    dchrval.b
    dchrval.u
    unitss
    #
    @33
    sseldi
    @27
    @29
    cE
    cc
    @34
    @27
    @28
    @23
    vk
    cU
    wral
    #
    cE
    cc
    wcel
    #
    @33
    wph
    @36
    @26
    wph
    @23
    vk
    cU
    dchrelbasd.5
    ralrimiva
    #
    adantr
    #
    @23
    @37
    vk
    @7
    cU
    @0
    @7
    wceq
    #
    cX
    cE
    cc
    dchrelbasd.3
    eleq1d
    rspcv
    sylc
    eqeltrd
    vk
    @7
    @2
    @29
    cB
    cc
    @3
    @40
    @1
    @28
    cX
    cE
    cc0
    @0
    @7
    cU
    eleq1
    dchrelbasd.3
    ifbieq1d
    @24
    fvmptg
    syl2anc
    @27
    @9
    cA
    @10
    cC
    cmul
    @27
    @9
    @18
    cA
    cc0
    cif
    #
    cA
    @27
    @4
    cB
    wcel
    #
    @41
    cc
    wcel
    #
    @9
    @41
    wceq
    #
    @27
    cU
    cB
    @4
    @35
    wph
    @18
    @25
    simprl
    #
    sseldi
    @27
    @41
    cA
    cc
    @18
    @41
    cA
    wceq
    wph
    @25
    @18
    cA
    cc0
    iftrue
    ad2antrl
    #
    @27
    @18
    @36
    cA
    cc
    wcel
    #
    @45
    @39
    @23
    @47
    vk
    @4
    cU
    @0
    @4
    wceq
    #
    cX
    cA
    cc
    dchrelbasd.1
    eleq1d
    rspcv
    #
    sylc
    eqeltrd
    vk
    @4
    @2
    @41
    cB
    cc
    @3
    @48
    @1
    @18
    cX
    cA
    cc0
    @0
    @4
    cU
    eleq1
    dchrelbasd.1
    ifbieq1d
    @24
    fvmptg
    #
    syl2anc
    @46
    eqtrd
    @27
    @10
    @25
    cC
    cc0
    cif
    #
    cC
    @27
    @5
    cB
    wcel
    @51
    cc
    wcel
    @10
    @51
    wceq
    @27
    cU
    cB
    @5
    @35
    wph
    @18
    @25
    simprr
    #
    sseldi
    @27
    @51
    cC
    cc
    @25
    @51
    cC
    wceq
    wph
    @18
    @25
    cC
    cc0
    iftrue
    ad2antll
    #
    @27
    @25
    @36
    cC
    cc
    wcel
    #
    @52
    @39
    @23
    @54
    vk
    @5
    cU
    @0
    @5
    wceq
    #
    cX
    cC
    cc
    dchrelbasd.2
    eleq1d
    rspcv
    sylc
    eqeltrd
    vk
    @5
    @2
    @51
    cB
    cc
    @3
    @55
    @1
    @25
    cX
    cC
    cc0
    @0
    @5
    cU
    eleq1
    dchrelbasd.2
    ifbieq1d
    @24
    fvmptg
    syl2anc
    @53
    eqtrd
    oveq12d
    3eqtr4d
    ralrimivva
    wph
    @15
    @14
    cU
    wcel
    #
    cY
    cc0
    cif
    #
    c1
    wph
    @14
    cB
    wcel
    @57
    cc
    wcel
    @15
    @57
    wceq
    wph
    cU
    cB
    @14
    @35
    wph
    @31
    @56
    @32
    cZ
    cU
    @14
    dchrval.u
    @14
    eqid
    1unit
    syl
    #
    sseldi
    wph
    @57
    c1
    cc
    wph
    @57
    cY
    c1
    wph
    @56
    cY
    cc0
    @58
    iftrued
    dchrelbasd.7
    eqtrd
    #
    ax-1cn
    syl6eqel
    vk
    @14
    @2
    @57
    cB
    cc
    @3
    @0
    @14
    wceq
    @1
    @56
    cX
    cY
    cc0
    @0
    @14
    cU
    eleq1
    dchrelbasd.4
    ifbieq1d
    @24
    fvmptg
    syl2anc
    @59
    eqtrd
    wph
    @19
    vx
    cB
    wph
    @42
    wa
    #
    @17
    @41
    cc0
    wne
    @18
    @60
    @9
    @41
    cc0
    @60
    @42
    @43
    @44
    wph
    @42
    simpr
    @60
    @18
    cA
    cc0
    cc
    wph
    @18
    @47
    @42
    wph
    @36
    @18
    @47
    @38
    @49
    mpan9
    adantlr
    @60
    @18
    wn
    wa
    0cnd
    ifclda
    @50
    syl2anc
    neeq1d
    @18
    @41
    cc0
    @18
    cA
    cc0
    iffalse
    necon1ai
    syl6bi
    ralrimiva
    3jca
    wph
    vx
    vy
    cB
    cD
    cU
    cG
    cN
    @3
    cZ
    dchrval.g
    dchrval.z
    dchrval.b
    dchrval.u
    dchrval.n
    dchrbas.b
    dchrelbas3
    mpbir2and
end
