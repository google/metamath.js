include "cfzo.mm"
include "co.mm"
include "cneg.mm"
include "cmin.mm"
include "csu.mm"
include "cv.mm"
include "wceq.mm"
include "negeqd.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "negcld.mm"
include "telfsumo.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "elfzofz.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "fzofzp1.mm"
include "neg2subd.mm"
include "sumeq2dv.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzfz1.mm"
include "syl.mm"
include "rspcv.mm"
include "sylc.mm"
include "eluzfz2.mm"
include "3eqtr3d.mm"

theorem telfsumo2
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
  assert |- ( ph -> sum_ j e. ( M ..^ N ) ( C - B ) = ( E - D ) )

  proof
    wph
    cM
    cN
    cfzo
    co
    #
    cB
    cneg
    #
    cC
    cneg
    #
    cmin
    co
    #
    vj
    csu
    cD
    cneg
    #
    cE
    cneg
    #
    cmin
    co
    @0
    cC
    cB
    cmin
    co
    #
    vj
    csu
    cE
    cD
    cmin
    co
    wph
    cA
    cneg
    @1
    @2
    @4
    vj
    vk
    @5
    cM
    cN
    vk
    cv
    #
    vj
    cv
    #
    wceq
    #
    cA
    cB
    telfsumo.1
    negeqd
    @7
    @8
    c1
    caddc
    co
    #
    wceq
    #
    cA
    cC
    telfsumo.2
    negeqd
    @7
    cM
    wceq
    #
    cA
    cD
    telfsumo.3
    negeqd
    @7
    cN
    wceq
    #
    cA
    cE
    telfsumo.4
    negeqd
    telfsumo.5
    wph
    @7
    cM
    cN
    cfz
    co
    #
    wcel
    wa
    cA
    telfsumo.6
    negcld
    telfsumo
    wph
    @0
    @3
    @6
    vj
    wph
    @8
    @0
    wcel
    #
    wa
    cB
    cC
    wph
    cA
    cc
    wcel
    #
    vk
    @14
    wral
    #
    @8
    @14
    wcel
    cB
    cc
    wcel
    #
    @15
    wph
    @16
    vk
    @14
    telfsumo.6
    ralrimiva
    #
    @8
    cM
    cN
    elfzofz
    @16
    @18
    vk
    @8
    @14
    @9
    cA
    cB
    cc
    telfsumo.1
    eleq1d
    rspccva
    syl2an
    wph
    @17
    @10
    @14
    wcel
    cC
    cc
    wcel
    #
    @15
    @19
    cM
    cN
    @8
    fzofzp1
    @16
    @20
    vk
    @10
    @14
    @11
    cA
    cC
    cc
    telfsumo.2
    eleq1d
    rspccva
    syl2an
    neg2subd
    sumeq2dv
    wph
    cD
    cE
    wph
    cM
    @14
    wcel
    #
    @17
    cD
    cc
    wcel
    #
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @21
    telfsumo.5
    cM
    cN
    eluzfz1
    syl
    @19
    @16
    @22
    vk
    cM
    @14
    @12
    cA
    cD
    cc
    telfsumo.3
    eleq1d
    rspcv
    sylc
    wph
    cN
    @14
    wcel
    #
    @17
    cE
    cc
    wcel
    #
    wph
    @23
    @24
    telfsumo.5
    cM
    cN
    eluzfz2
    syl
    @19
    @16
    @25
    vk
    cN
    @14
    @13
    cA
    cE
    cc
    telfsumo.4
    eleq1d
    rspcv
    sylc
    neg2subd
    3eqtr3d
end
