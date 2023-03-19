include "cfz.mm"
include "co.mm"
include "csu.mm"
include "csn.mm"
include "c1.mm"
include "caddc.mm"
include "cin.mm"
include "c0.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzel2.mm"
include "syl.mm"
include "fzsn.mm"
include "ineq1d.mm"
include "clt.mm"
include "wbr.mm"
include "zred.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "eqtr3d.mm"
include "cun.mm"
include "eluzfz1.mm"
include "fzsplit.mm"
include "uneq1d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "fsumsplit.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "oveq1d.mm"

theorem fsum1p
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fsumm1.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsumm1.2: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )
  assume fsum1p.3: |- ( k = M -> A = B )

  disjoint B k
  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> sum_ k e. ( M ... N ) A = ( B + sum_ k e. ( ( M + 1 ) ... N ) A ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cA
    vk
    csu
    cM
    csn
    #
    cA
    vk
    csu
    #
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cA
    vk
    csu
    #
    caddc
    co
    cB
    @5
    caddc
    co
    wph
    @1
    @4
    cA
    @0
    vk
    wph
    cM
    cM
    cfz
    co
    #
    @4
    cin
    #
    @1
    @4
    cin
    c0
    wph
    @6
    @1
    @4
    wph
    cM
    cz
    wcel
    #
    @6
    @1
    wceq
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @8
    fsumm1.1
    cM
    cN
    eluzel2
    syl
    #
    cM
    fzsn
    syl
    #
    ineq1d
    wph
    cM
    @3
    clt
    wbr
    @7
    c0
    wceq
    wph
    cM
    wph
    cM
    @10
    zred
    ltp1d
    cM
    cM
    @3
    cN
    fzdisj
    syl
    eqtr3d
    wph
    @0
    @6
    @4
    cun
    #
    @1
    @4
    cun
    wph
    cM
    @0
    wcel
    #
    @0
    @12
    wceq
    wph
    @9
    @13
    fsumm1.1
    cM
    cN
    eluzfz1
    syl
    #
    cM
    cM
    cN
    fzsplit
    syl
    wph
    @6
    @1
    @4
    @11
    uneq1d
    eqtrd
    wph
    cM
    cN
    fzfid
    fsumm1.2
    fsumsplit
    wph
    @2
    cB
    @5
    caddc
    wph
    @8
    cB
    cc
    wcel
    #
    @2
    cB
    wceq
    @10
    wph
    @13
    cA
    cc
    wcel
    #
    vk
    @0
    wral
    @15
    @14
    wph
    @16
    vk
    @0
    fsumm1.2
    ralrimiva
    @16
    @15
    vk
    cM
    @0
    vk
    cv
    cM
    wceq
    cA
    cB
    cc
    fsum1p.3
    eleq1d
    rspcv
    sylc
    cA
    cB
    vk
    cM
    cz
    fsum1p.3
    sumsn
    syl2anc
    oveq1d
    eqtrd
end
