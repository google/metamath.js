include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cbc.mm"
include "c1.mm"
include "cneg.mm"
include "cmin.mm"
include "cexp.mm"
include "caddc.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "cdm.mm"
include "wcel.mm"
include "wral.mm"
include "cc.mm"
include "crab.mm"
include "cfwddifn.mm"
include "cvv.mm"
include "cn0.mm"
include "cpm.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-fwddifn.mm"
include "a1i.mm"
include "wa.mm"
include "oveq2.mm"
include "adantr.mm"
include "wb.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "adantl.mm"
include "raleqbidv.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "oveq12d.mm"
include "sumeq12dv.mm"
include "mpteq12dv.mm"
include "wf.mm"
include "wss.mm"
include "cnex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "mptrabex.mm"
include "ovmpt2d.mm"
include "fveq2d.mm"
include "sumeq2sdv.mm"
include "fdm.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "sumex.mm"
include "fvmptd.mm"

theorem fwddifnval
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cX: class X
  let vn: setvar n
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume fwddifnval.1: |- ( ph -> N e. NN0 )
  assume fwddifnval.2: |- ( ph -> A C_ CC )
  assume fwddifnval.3: |- ( ph -> F : A --> CC )
  assume fwddifnval.4: |- ( ph -> X e. CC )
  assume fwddifnval.5: |- ( ( ph /\ k e. ( 0 ... N ) ) -> ( X + k ) e. A )

  disjoint N k
  disjoint A k
  disjoint X k
  disjoint F k
  disjoint k ph
  disjoint N n
  disjoint N f
  disjoint N x
  disjoint N y
  disjoint f n
  disjoint k n
  disjoint n x
  disjoint n y
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint A n
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint X n
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint F n
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint n ph
  disjoint f ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ( N _/_\^n F ) ` X ) = sum_ k e. ( 0 ... N ) ( ( N _C k ) x. ( ( -u 1 ^ ( N - k ) ) x. ( F ` ( X + k ) ) ) ) )

  proof
    wph
    vx
    cX
    cc0
    cN
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    c1
    cneg
    #
    cN
    @1
    cmin
    co
    #
    cexp
    co
    #
    vx
    cv
    #
    @1
    caddc
    co
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @0
    @2
    @5
    cX
    @1
    caddc
    co
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    vy
    cv
    #
    @1
    caddc
    co
    #
    cF
    cdm
    #
    wcel
    #
    vk
    @0
    wral
    #
    vy
    cc
    crab
    #
    cN
    cF
    cfwddifn
    co
    cvv
    wph
    vn
    vf
    cN
    cF
    cn0
    cc
    cc
    cpm
    co
    #
    vx
    @18
    vf
    cv
    #
    cdm
    #
    wcel
    #
    vk
    cc0
    vn
    cv
    #
    cfz
    co
    #
    wral
    #
    vy
    cc
    crab
    #
    @28
    @27
    @1
    cbc
    co
    #
    @3
    @27
    @1
    cmin
    co
    #
    cexp
    co
    #
    @7
    @24
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    vx
    @22
    @11
    cmpt
    #
    cfwddifn
    cvv
    cfwddifn
    vn
    vf
    cn0
    @23
    @38
    cmpt2
    wceq
    wph
    vx
    vy
    vf
    vk
    vn
    df-fwddifn
    a1i
    @27
    cN
    wceq
    #
    @24
    cF
    wceq
    #
    wa
    #
    @38
    @39
    wceq
    wph
    @42
    vx
    @30
    @37
    @22
    @11
    @42
    @29
    @21
    vy
    cc
    @42
    @26
    @20
    vk
    @28
    @0
    @40
    @28
    @0
    wceq
    @41
    @27
    cN
    cc0
    cfz
    oveq2
    adantr
    #
    @41
    @26
    @20
    wb
    @40
    @41
    @25
    @19
    @18
    @24
    cF
    dmeq
    eleq2d
    adantl
    raleqbidv
    rabbidv
    @42
    @28
    @0
    @36
    @10
    vk
    @43
    @42
    @36
    @10
    wceq
    @1
    @28
    wcel
    @42
    @31
    @2
    @35
    @9
    cmul
    @40
    @31
    @2
    wceq
    @41
    @27
    cN
    @1
    cbc
    oveq1
    adantr
    @40
    @41
    @33
    @5
    @34
    @8
    cmul
    @40
    @32
    @4
    @3
    cexp
    @27
    cN
    @1
    cmin
    oveq1
    oveq2d
    @7
    @24
    cF
    fveq1
    oveqan12d
    oveq12d
    adantr
    sumeq12dv
    mpteq12dv
    adantl
    fwddifnval.1
    wph
    cA
    cc
    cF
    wf
    #
    cA
    cc
    wss
    #
    cF
    @23
    wcel
    #
    fwddifnval.3
    fwddifnval.2
    cc
    cvv
    wcel
    #
    @47
    @44
    @45
    wa
    @46
    cnex
    cnex
    cc
    cc
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anc
    @39
    cvv
    wcel
    wph
    @21
    vx
    vy
    cc
    @11
    cnex
    mptrabex
    a1i
    ovmpt2d
    @6
    cX
    wceq
    #
    @11
    @16
    wceq
    wph
    @48
    @0
    @10
    @15
    vk
    @48
    @9
    @14
    @2
    cmul
    @48
    @8
    @13
    @5
    cmul
    @48
    @7
    @12
    cF
    @6
    cX
    @1
    caddc
    oveq1
    fveq2d
    oveq2d
    oveq2d
    sumeq2sdv
    adantl
    wph
    cX
    cc
    wcel
    @12
    @19
    wcel
    #
    vk
    @0
    wral
    #
    cX
    @22
    wcel
    fwddifnval.4
    wph
    @49
    vk
    @0
    wph
    @1
    @0
    wcel
    #
    wa
    @12
    cA
    @19
    fwddifnval.5
    wph
    @19
    cA
    wceq
    #
    @51
    wph
    @44
    @52
    fwddifnval.3
    cA
    cc
    cF
    fdm
    syl
    adantr
    eleqtrrd
    ralrimiva
    @21
    @50
    vy
    cX
    cc
    @17
    cX
    wceq
    #
    @20
    @49
    vk
    @0
    @53
    @18
    @12
    @19
    @17
    cX
    @1
    caddc
    oveq1
    eleq1d
    ralbidv
    elrab
    sylanbrc
    @16
    cvv
    wcel
    wph
    @0
    @15
    vk
    sumex
    a1i
    fvmptd
end
