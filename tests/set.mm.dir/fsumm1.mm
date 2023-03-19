include "cfz.mm"
include "co.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "csn.mm"
include "caddc.mm"
include "cin.mm"
include "c0.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzelz.mm"
include "syl.mm"
include "fzsn.mm"
include "ineq2d.mm"
include "clt.mm"
include "wbr.mm"
include "zred.mm"
include "ltm1d.mm"
include "fzdisj.mm"
include "eqtr3d.mm"
include "cun.mm"
include "eluzel2.mm"
include "peano2zm.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "eluzp1m1.mm"
include "syl2anc.mm"
include "fzsuc2.mm"
include "oveq2d.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "fzfid.mm"
include "fsumsplit.mm"
include "wral.mm"
include "eluzfz2.mm"
include "ralrimiva.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sumsn.mm"
include "eqtrd.mm"

theorem fsumm1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fsumm1.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsumm1.2: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )
  assume fsumm1.3: |- ( k = N -> A = B )

  disjoint B k
  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> sum_ k e. ( M ... N ) A = ( sum_ k e. ( M ... ( N - 1 ) ) A + B ) )

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
    #
    cN
    csn
    #
    cA
    vk
    csu
    #
    caddc
    co
    @3
    cB
    caddc
    co
    wph
    @2
    @4
    cA
    @0
    vk
    wph
    @2
    cN
    cN
    cfz
    co
    #
    cin
    #
    @2
    @4
    cin
    c0
    wph
    @6
    @4
    @2
    wph
    cN
    cz
    wcel
    #
    @6
    @4
    wceq
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @8
    fsumm1.1
    cM
    cN
    eluzelz
    syl
    #
    cN
    fzsn
    syl
    ineq2d
    wph
    @1
    cN
    clt
    wbr
    @7
    c0
    wceq
    wph
    cN
    wph
    cN
    @11
    zred
    ltm1d
    cM
    @1
    cN
    cN
    fzdisj
    syl
    eqtr3d
    wph
    @2
    @1
    c1
    caddc
    co
    #
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
    @12
    cfz
    co
    #
    @14
    @0
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
    @15
    @14
    wceq
    wph
    @10
    @16
    fsumm1.1
    cM
    cN
    eluzel2
    syl
    #
    wph
    @17
    cz
    wcel
    #
    cN
    @17
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @18
    wph
    @16
    @20
    @19
    cM
    peano2zm
    syl
    wph
    cN
    @9
    @22
    fsumm1.1
    wph
    @21
    cM
    cuz
    wph
    cM
    cc
    wcel
    c1
    cc
    wcel
    #
    @21
    cM
    wceq
    wph
    cM
    @19
    zcnd
    ax-1cn
    cM
    c1
    npcan
    sylancl
    fveq2d
    eleqtrrd
    @17
    cN
    eluzp1m1
    syl2anc
    cM
    @1
    fzsuc2
    syl2anc
    wph
    @12
    cN
    cM
    cfz
    wph
    cN
    cc
    wcel
    @23
    @12
    cN
    wceq
    wph
    cN
    @11
    zcnd
    ax-1cn
    cN
    c1
    npcan
    sylancl
    #
    oveq2d
    eqtr3d
    wph
    @13
    @4
    @2
    wph
    @12
    cN
    @24
    sneqd
    uneq2d
    eqtr3d
    wph
    cM
    cN
    fzfid
    fsumm1.2
    fsumsplit
    wph
    @5
    cB
    @3
    caddc
    wph
    @10
    cB
    cc
    wcel
    #
    @5
    cB
    wceq
    fsumm1.1
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
    @25
    wph
    @10
    @26
    fsumm1.1
    cM
    cN
    eluzfz2
    syl
    wph
    @27
    vk
    @0
    fsumm1.2
    ralrimiva
    @27
    @25
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
    fsumm1.3
    eleq1d
    rspcv
    sylc
    cA
    cB
    vk
    cN
    @9
    fsumm1.3
    sumsn
    syl2anc
    oveq2d
    eqtrd
end
