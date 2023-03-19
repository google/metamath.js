include "wceq.mm"
include "cfzo.mm"
include "co.mm"
include "cmin.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cc0.mm"
include "cc.mm"
include "cfz.mm"
include "wral.mm"
include "eluzfz1.mm"
include "syl.mm"
include "ralrimiva.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "adantr.mm"
include "subidd.mm"
include "sum0.mm"
include "syl6reqr.mm"
include "oveq2.mm"
include "adantl.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "sumeq1d.mm"
include "wi.mm"
include "eqeq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "imp.mm"
include "sylan.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "elfzofz.mm"
include "fzofzp1.mm"
include "fsumsub.mm"
include "cbvsumv.mm"
include "cz.mm"
include "eluzel2.mm"
include "eluzp1m1.mm"
include "eluzelz.mm"
include "fzoval.mm"
include "fzossfz.mm"
include "syl6eqssr.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "fsum1p.mm"
include "syl5eqr.mm"
include "simpr.mm"
include "wss.mm"
include "fzp1ss.mm"
include "fsumm1.mm"
include "1zzd.mm"
include "peano2zd.mm"
include "fsumshftm.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "eqtrd.mm"
include "sylan2.mm"
include "fsumcl.mm"
include "eluzfz2.mm"
include "addcomd.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "oveq12d.mm"
include "pnpcan2d.mm"
include "wo.mm"
include "uzp1.mm"
include "mpjaodan.mm"

theorem telfsumo
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cM: class M
  let cN: class N
  assume telfsumo.1: |- ( k = j -> A = B )
  assume telfsumo.2: |- ( k = ( j + 1 ) -> A = C )
  assume telfsumo.3: |- ( k = M -> A = D )
  assume telfsumo.4: |- ( k = N -> A = E )
  assume telfsumo.5: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume telfsumo.6: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )

  disjoint A j
  disjoint B k
  disjoint C k
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  disjoint D k
  disjoint E k
  assert |- ( ph -> sum_ j e. ( M ..^ N ) ( B - C ) = ( D - E ) )

  proof
    wph
    cN
    cM
    wceq
    #
    cM
    cN
    cfzo
    co
    #
    cB
    cC
    cmin
    co
    #
    vj
    csu
    #
    cD
    cE
    cmin
    co
    #
    wceq
    cN
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    wph
    @0
    wa
    #
    c0
    @2
    vj
    csu
    #
    cD
    cD
    cmin
    co
    #
    @3
    @4
    @7
    @9
    cc0
    @8
    @7
    cD
    wph
    cD
    cc
    wcel
    #
    @0
    wph
    cM
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cA
    cc
    wcel
    #
    vk
    @11
    wral
    #
    @10
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @12
    telfsumo.5
    cM
    cN
    eluzfz1
    syl
    wph
    @13
    vk
    @11
    telfsumo.6
    ralrimiva
    #
    @13
    @10
    vk
    cM
    @11
    vk
    cv
    #
    cM
    wceq
    #
    cA
    cD
    cc
    telfsumo.3
    eleq1d
    rspcv
    sylc
    #
    adantr
    subidd
    @2
    vj
    sum0
    syl6reqr
    @7
    @1
    c0
    @2
    vj
    @7
    @1
    cM
    cM
    cfzo
    co
    #
    c0
    @0
    @1
    @21
    wceq
    wph
    cN
    cM
    cM
    cfzo
    oveq2
    adantl
    cM
    fzo0
    syl6eq
    sumeq1d
    @7
    cE
    cD
    cD
    cmin
    wph
    @16
    @0
    cE
    cD
    wceq
    #
    telfsumo.5
    @16
    @0
    @22
    @19
    cA
    cD
    wceq
    #
    wi
    @0
    @22
    wi
    vk
    cN
    @15
    @18
    cN
    wceq
    #
    @19
    @0
    @23
    @22
    @18
    cN
    cM
    eqeq1
    @24
    cA
    cE
    cD
    telfsumo.4
    eqeq1d
    imbi12d
    telfsumo.3
    vtoclg
    imp
    sylan
    oveq2d
    3eqtr4d
    wph
    @6
    wa
    #
    @3
    @1
    cB
    vj
    csu
    #
    @1
    cC
    vj
    csu
    #
    cmin
    co
    #
    @4
    wph
    @3
    @28
    wceq
    @6
    wph
    @1
    cB
    cC
    vj
    @1
    cfn
    wcel
    wph
    cM
    cN
    fzofi
    a1i
    wph
    vj
    cv
    #
    @1
    wcel
    #
    wa
    #
    @29
    @11
    wcel
    #
    @14
    cB
    cc
    wcel
    #
    @30
    @32
    wph
    @29
    cM
    cN
    elfzofz
    adantl
    wph
    @14
    @30
    @17
    adantr
    #
    @13
    @33
    vk
    @29
    @11
    @18
    @29
    wceq
    cA
    cB
    cc
    telfsumo.1
    eleq1d
    rspcv
    sylc
    @31
    @29
    c1
    caddc
    co
    #
    @11
    wcel
    #
    @14
    cC
    cc
    wcel
    #
    @30
    @36
    wph
    cM
    cN
    @29
    fzofzp1
    adantl
    @34
    @13
    @37
    vk
    @35
    @11
    @18
    @35
    wceq
    cA
    cC
    cc
    telfsumo.2
    eleq1d
    rspcv
    sylc
    fsumsub
    adantr
    @25
    @28
    cD
    @5
    cN
    cfzo
    co
    #
    cA
    vk
    csu
    #
    caddc
    co
    #
    cE
    @39
    caddc
    co
    #
    cmin
    co
    #
    @4
    @25
    @26
    @40
    @27
    @41
    cmin
    @25
    @26
    @1
    cA
    vk
    csu
    #
    @40
    @1
    cA
    cB
    vk
    vj
    telfsumo.1
    cbvsumv
    @25
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    csu
    cD
    @5
    @44
    cfz
    co
    #
    cA
    vk
    csu
    #
    caddc
    co
    @43
    @40
    @25
    cA
    cD
    vk
    cM
    @44
    wph
    cM
    cz
    wcel
    #
    @6
    @44
    @15
    wcel
    wph
    @16
    @48
    telfsumo.5
    cM
    cN
    eluzel2
    syl
    #
    cM
    cN
    eluzp1m1
    sylan
    @25
    @18
    @45
    wcel
    @18
    @11
    wcel
    #
    @13
    @25
    @45
    @11
    @18
    @25
    @45
    @1
    @11
    @25
    cN
    cz
    wcel
    #
    @1
    @45
    wceq
    #
    wph
    @51
    @6
    wph
    @16
    @51
    telfsumo.5
    cM
    cN
    eluzelz
    syl
    #
    adantr
    #
    cM
    cN
    fzoval
    #
    syl
    #
    cM
    cN
    fzossfz
    syl6eqssr
    sselda
    wph
    @50
    @13
    @6
    telfsumo.6
    adantlr
    syldan
    telfsumo.3
    fsum1p
    @25
    @1
    @45
    cA
    vk
    @56
    sumeq1d
    @25
    @39
    @47
    cD
    caddc
    @25
    @38
    @46
    cA
    vk
    @25
    @51
    @38
    @46
    wceq
    #
    @54
    @5
    cN
    fzoval
    #
    syl
    sumeq1d
    oveq2d
    3eqtr4d
    syl5eqr
    @25
    @5
    cN
    cfz
    co
    #
    cA
    vk
    csu
    #
    @47
    cE
    caddc
    co
    #
    @27
    @41
    @25
    cA
    cE
    vk
    @5
    cN
    wph
    @6
    simpr
    wph
    @18
    @59
    wcel
    #
    @13
    @6
    wph
    @62
    @50
    @13
    wph
    @59
    @11
    @18
    wph
    @48
    @59
    @11
    wss
    @49
    cM
    cN
    fzp1ss
    syl
    sselda
    telfsumo.6
    syldan
    #
    adantlr
    telfsumo.4
    fsumm1
    wph
    @60
    @27
    wceq
    @6
    wph
    @60
    @5
    c1
    cmin
    co
    #
    @44
    cfz
    co
    #
    cC
    vj
    csu
    @27
    wph
    cA
    cC
    vk
    vj
    c1
    @5
    cN
    wph
    1zzd
    wph
    cM
    @49
    peano2zd
    @53
    @63
    telfsumo.2
    fsumshftm
    wph
    @65
    @1
    cC
    vj
    wph
    @65
    @45
    @1
    wph
    @64
    cM
    @44
    cfz
    wph
    cM
    cc
    wcel
    c1
    cc
    wcel
    @64
    cM
    wceq
    wph
    cM
    @49
    zcnd
    ax-1cn
    cM
    c1
    pncan
    sylancl
    oveq1d
    wph
    @51
    @52
    @53
    @55
    syl
    eqtr4d
    sumeq1d
    eqtrd
    adantr
    wph
    @61
    @41
    wceq
    @6
    wph
    @39
    cE
    caddc
    co
    @61
    @41
    wph
    @39
    @47
    cE
    caddc
    wph
    @38
    @46
    cA
    vk
    wph
    @51
    @57
    @53
    @58
    syl
    sumeq1d
    oveq1d
    wph
    @39
    cE
    wph
    @38
    cA
    vk
    @38
    cfn
    wcel
    wph
    @5
    cN
    fzofi
    a1i
    @18
    @38
    wcel
    wph
    @62
    @13
    @18
    @5
    cN
    elfzofz
    @63
    sylan2
    fsumcl
    #
    wph
    cN
    @11
    wcel
    #
    @14
    cE
    cc
    wcel
    #
    wph
    @16
    @67
    telfsumo.5
    cM
    cN
    eluzfz2
    syl
    @17
    @13
    @68
    vk
    cN
    @11
    @24
    cA
    cE
    cc
    telfsumo.4
    eleq1d
    rspcv
    sylc
    #
    addcomd
    eqtr3d
    adantr
    3eqtr3d
    oveq12d
    wph
    @42
    @4
    wceq
    @6
    wph
    cD
    cE
    @39
    @20
    @69
    @66
    pnpcan2d
    adantr
    eqtrd
    eqtrd
    wph
    @16
    @0
    @6
    wo
    telfsumo.5
    cM
    cN
    uzp1
    syl
    mpjaodan
end
