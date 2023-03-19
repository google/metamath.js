include "cz.mm"
include "wcel.mm"
include "wral.mm"
include "cn.mm"
include "csu.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cfn.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "raleq.mm"
include "anbi1d.mm"
include "sumeq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "weq.mm"
include "cc0.mm"
include "sum0.mm"
include "a1i.mm"
include "oveq1i.mm"
include "syl6reqr.mm"
include "adantl.mm"
include "simpll.mm"
include "simplrr.mm"
include "ralun.mm"
include "ex.mm"
include "ad2antrl.mm"
include "imp.mm"
include "modfsummods.mm"
include "syl3anc.mm"
include "com23.mm"
include "a2d.mm"
include "ralunb.mm"
include "anbi1i.mm"
include "imbi1i.mm"
include "an32.mm"
include "impexp.mm"
include "3bitri.mm"
include "syl6ibr.mm"
include "findcard2.mm"
include "syl.mm"
include "mp2and.mm"

theorem modfsummod
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume modfsummod.n: |- ( ph -> N e. NN )
  assume modfsummod.1: |- ( ph -> A e. Fin )
  assume modfsummod.2: |- ( ph -> A. k e. A B e. ZZ )

  disjoint A k
  disjoint N k
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( ph -> ( sum_ k e. A B mod N ) = ( sum_ k e. A ( B mod N ) mod N ) )

  proof
    wph
    cB
    cz
    wcel
    #
    vk
    cA
    wral
    #
    cN
    cn
    wcel
    #
    cA
    cB
    vk
    csu
    #
    cN
    cmo
    co
    #
    cA
    cB
    cN
    cmo
    co
    #
    vk
    csu
    #
    cN
    cmo
    co
    #
    wceq
    #
    modfsummod.2
    modfsummod.n
    wph
    cA
    cfn
    wcel
    @1
    @2
    wa
    #
    @8
    wi
    #
    modfsummod.1
    @0
    vk
    vx
    cv
    #
    wral
    #
    @2
    wa
    #
    @11
    cB
    vk
    csu
    #
    cN
    cmo
    co
    #
    @11
    @5
    vk
    csu
    #
    cN
    cmo
    co
    #
    wceq
    #
    wi
    @0
    vk
    c0
    wral
    #
    @2
    wa
    #
    c0
    cB
    vk
    csu
    #
    cN
    cmo
    co
    #
    c0
    @5
    vk
    csu
    #
    cN
    cmo
    co
    #
    wceq
    #
    wi
    @0
    vk
    vy
    cv
    #
    wral
    #
    @2
    wa
    #
    @26
    cB
    vk
    csu
    #
    cN
    cmo
    co
    #
    @26
    @5
    vk
    csu
    #
    cN
    cmo
    co
    #
    wceq
    #
    wi
    #
    @0
    vk
    @26
    vz
    cv
    csn
    #
    cun
    #
    wral
    #
    @2
    wa
    #
    @36
    cB
    vk
    csu
    #
    cN
    cmo
    co
    #
    @36
    @5
    vk
    csu
    #
    cN
    cmo
    co
    #
    wceq
    #
    wi
    #
    @10
    vx
    vy
    vz
    cA
    @11
    c0
    wceq
    #
    @13
    @20
    @18
    @25
    @45
    @12
    @19
    @2
    @0
    vk
    @11
    c0
    raleq
    anbi1d
    @45
    @15
    @22
    @17
    @24
    @45
    @14
    @21
    cN
    cmo
    @11
    c0
    cB
    vk
    sumeq1
    oveq1d
    @45
    @16
    @23
    cN
    cmo
    @11
    c0
    @5
    vk
    sumeq1
    oveq1d
    eqeq12d
    imbi12d
    vx
    vy
    weq
    #
    @13
    @28
    @18
    @33
    @46
    @12
    @27
    @2
    @0
    vk
    @11
    @26
    raleq
    anbi1d
    @46
    @15
    @30
    @17
    @32
    @46
    @14
    @29
    cN
    cmo
    @11
    @26
    cB
    vk
    sumeq1
    oveq1d
    @46
    @16
    @31
    cN
    cmo
    @11
    @26
    @5
    vk
    sumeq1
    oveq1d
    eqeq12d
    imbi12d
    @11
    @36
    wceq
    #
    @13
    @38
    @18
    @43
    @47
    @12
    @37
    @2
    @0
    vk
    @11
    @36
    raleq
    anbi1d
    @47
    @15
    @40
    @17
    @42
    @47
    @14
    @39
    cN
    cmo
    @11
    @36
    cB
    vk
    sumeq1
    oveq1d
    @47
    @16
    @41
    cN
    cmo
    @11
    @36
    @5
    vk
    sumeq1
    oveq1d
    eqeq12d
    imbi12d
    @11
    cA
    wceq
    #
    @13
    @9
    @18
    @8
    @48
    @12
    @1
    @2
    @0
    vk
    @11
    cA
    raleq
    anbi1d
    @48
    @15
    @4
    @17
    @7
    @48
    @14
    @3
    cN
    cmo
    @11
    cA
    cB
    vk
    sumeq1
    oveq1d
    @48
    @16
    @6
    cN
    cmo
    @11
    cA
    @5
    vk
    sumeq1
    oveq1d
    eqeq12d
    imbi12d
    @2
    @25
    @19
    @2
    @24
    cc0
    cN
    cmo
    co
    @22
    @2
    @23
    cc0
    cN
    cmo
    @23
    cc0
    wceq
    @2
    @5
    vk
    sum0
    a1i
    oveq1d
    @21
    cc0
    cN
    cmo
    cB
    vk
    sum0
    oveq1i
    syl6reqr
    adantl
    @26
    cfn
    wcel
    #
    @34
    @28
    @0
    vk
    @35
    wral
    #
    @43
    wi
    #
    wi
    #
    @44
    @49
    @28
    @33
    @51
    @49
    @28
    @33
    @51
    wi
    @49
    @28
    wa
    #
    @50
    @33
    @43
    @53
    @50
    @33
    @43
    wi
    #
    @53
    @50
    wa
    @49
    @2
    @37
    @54
    @49
    @28
    @50
    simpll
    @49
    @27
    @2
    @50
    simplrr
    @53
    @50
    @37
    @27
    @50
    @37
    wi
    @49
    @2
    @27
    @50
    @37
    @0
    vk
    @26
    @35
    ralun
    ex
    ad2antrl
    imp
    vz
    @26
    cB
    vk
    cN
    modfsummods
    syl3anc
    ex
    com23
    ex
    a2d
    @44
    @27
    @50
    wa
    #
    @2
    wa
    #
    @43
    wi
    @28
    @50
    wa
    #
    @43
    wi
    @52
    @38
    @56
    @43
    @37
    @55
    @2
    @0
    vk
    @26
    @35
    ralunb
    anbi1i
    imbi1i
    @56
    @57
    @43
    @27
    @50
    @2
    an32
    imbi1i
    @28
    @50
    @43
    impexp
    3bitri
    syl6ibr
    findcard2
    syl
    mp2and
end
