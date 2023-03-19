include "cfz.mm"
include "co.mm"
include "cprod.mm"
include "csn.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "cin.mm"
include "c0.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzfz1.mm"
include "syl.mm"
include "elfzelz.mm"
include "fzsn.mm"
include "ineq1d.mm"
include "clt.mm"
include "wbr.mm"
include "zred.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "eqtr3d.mm"
include "cun.mm"
include "fzsplit.mm"
include "uneq1d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "fprodsplit.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "prodsn.mm"
include "syl2anc.mm"
include "oveq1d.mm"

theorem fprod1p
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fprod1p.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fprod1p.2: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )
  assume fprod1p.3: |- ( k = M -> A = B )

  disjoint B k
  disjoint k ph
  disjoint M k
  disjoint N k
  assert |- ( ph -> prod_ k e. ( M ... N ) A = ( B x. prod_ k e. ( ( M + 1 ) ... N ) A ) )

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
    csn
    #
    cA
    vk
    cprod
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
    cprod
    #
    cmul
    co
    cB
    @5
    cmul
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
    cM
    @0
    wcel
    #
    @8
    wph
    cN
    cM
    cuz
    cfv
    wcel
    @9
    fprod1p.1
    cM
    cN
    eluzfz1
    syl
    #
    cM
    cM
    cN
    elfzelz
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
    @11
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
    @9
    @0
    @13
    wceq
    @10
    cM
    cM
    cN
    fzsplit
    syl
    wph
    @6
    @1
    @4
    @12
    uneq1d
    eqtrd
    wph
    cM
    cN
    fzfid
    fprod1p.2
    fprodsplit
    wph
    @2
    cB
    @5
    cmul
    wph
    @9
    cB
    cc
    wcel
    #
    @2
    cB
    wceq
    @10
    wph
    @9
    cA
    cc
    wcel
    #
    vk
    @0
    wral
    @14
    @10
    wph
    @15
    vk
    @0
    fprod1p.2
    ralrimiva
    @15
    @14
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
    fprod1p.3
    eleq1d
    rspcv
    sylc
    cA
    cB
    vk
    cM
    @0
    fprod1p.3
    prodsn
    syl2anc
    oveq1d
    eqtrd
end
