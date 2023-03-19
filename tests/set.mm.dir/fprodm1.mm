include "cfz.mm"
include "co.mm"
include "cprod.mm"
include "c1.mm"
include "cmin.mm"
include "csn.mm"
include "cmul.mm"
include "wcel.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "caddc.mm"
include "fzp1nel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "eluzelz.mm"
include "syl.mm"
include "zcnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "eleq1d.mm"
include "mtbii.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cun.mm"
include "eluzel2.mm"
include "peano2zm.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "eluzp1m1.mm"
include "syl2anc.mm"
include "fzsuc2.mm"
include "oveq2d.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "3eqtr3d.mm"
include "fzfid.mm"
include "fprodsplit.mm"
include "cc.mm"
include "wral.mm"
include "eluzfz2.mm"
include "ralrimiva.mm"
include "cv.mm"
include "rspcv.mm"
include "sylc.mm"
include "prodsn.mm"
include "eqtrd.mm"

theorem fprodm1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fprodm1.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fprodm1.2: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )
  assume fprodm1.3: |- ( k = N -> A = B )

  disjoint B k
  disjoint k ph
  disjoint M k
  disjoint N k
  assert |- ( ph -> prod_ k e. ( M ... N ) A = ( prod_ k e. ( M ... ( N - 1 ) ) A x. B ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cA
    vk
    cprod
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
    cprod
    #
    cN
    csn
    #
    cA
    vk
    cprod
    #
    cmul
    co
    @3
    cB
    cmul
    co
    wph
    @2
    @4
    cA
    @0
    vk
    wph
    cN
    @2
    wcel
    #
    wn
    @2
    @4
    cin
    c0
    wceq
    wph
    @1
    c1
    caddc
    co
    #
    @2
    wcel
    @6
    cM
    @1
    fzp1nel
    wph
    @7
    cN
    @2
    wph
    cN
    c1
    wph
    cN
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    fprodm1.1
    cM
    cN
    eluzelz
    syl
    zcnd
    wph
    1cnd
    #
    npcand
    #
    eleq1d
    mtbii
    @2
    cN
    disjsn
    sylibr
    wph
    cM
    @7
    cfz
    co
    #
    @2
    @7
    csn
    #
    cun
    #
    @0
    @2
    @4
    cun
    wph
    cM
    cz
    wcel
    #
    @1
    cM
    c1
    cmin
    co
    #
    cuz
    cfv
    wcel
    #
    @12
    @14
    wceq
    wph
    @9
    @15
    fprodm1.1
    cM
    cN
    eluzel2
    syl
    #
    wph
    @16
    cz
    wcel
    #
    cN
    @16
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @17
    wph
    @15
    @19
    @18
    cM
    peano2zm
    syl
    wph
    cN
    @8
    @21
    fprodm1.1
    wph
    @20
    cM
    cuz
    wph
    cM
    c1
    wph
    cM
    @18
    zcnd
    @10
    npcand
    fveq2d
    eleqtrrd
    @16
    cN
    eluzp1m1
    syl2anc
    cM
    @1
    fzsuc2
    syl2anc
    wph
    @7
    cN
    cM
    cfz
    @11
    oveq2d
    wph
    @13
    @4
    @2
    wph
    @7
    cN
    @11
    sneqd
    uneq2d
    3eqtr3d
    wph
    cM
    cN
    fzfid
    fprodm1.2
    fprodsplit
    wph
    @5
    cB
    @3
    cmul
    wph
    @9
    cB
    cc
    wcel
    #
    @5
    cB
    wceq
    fprodm1.1
    wph
    cN
    @0
    wcel
    #
    cA
    cc
    wcel
    #
    vk
    @0
    wral
    @22
    wph
    @9
    @23
    fprodm1.1
    cM
    cN
    eluzfz2
    syl
    wph
    @24
    vk
    @0
    fprodm1.2
    ralrimiva
    @24
    @22
    vk
    cN
    @0
    vk
    cv
    cN
    wceq
    cA
    cB
    cc
    fprodm1.3
    eleq1d
    rspcv
    sylc
    cA
    cB
    vk
    cN
    @8
    fprodm1.3
    prodsn
    syl2anc
    oveq2d
    eqtrd
end
