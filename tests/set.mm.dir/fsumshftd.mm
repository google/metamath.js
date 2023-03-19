include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cv.mm"
include "csb.mm"
include "caddc.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "cmin.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wi.mm"
include "nfv.mm"
include "nfel1.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "csbeq1.mm"
include "fsumshft.mm"
include "cvv.mm"
include "ovexd.mm"
include "csbied.mm"
include "sumeq2sdv.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem fsumshftd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vw: setvar w
  assume fsumshftd.1: |- ( ph -> K e. ZZ )
  assume fsumshftd.2: |- ( ph -> M e. ZZ )
  assume fsumshftd.3: |- ( ph -> N e. ZZ )
  assume fsumshftd.4: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. CC )
  assume fsumshftd.5: |- ( ( ph /\ j = ( k - K ) ) -> A = B )

  disjoint A k
  disjoint B j
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  disjoint k w
  disjoint A w
  disjoint j w
  disjoint K w
  disjoint M w
  disjoint N w
  disjoint ph w
  assert |- ( ph -> sum_ j e. ( M ... N ) A = sum_ k e. ( ( M + K ) ... ( N + K ) ) B )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cA
    vj
    csu
    @0
    vj
    vw
    cv
    #
    cA
    csb
    #
    vw
    csu
    #
    cM
    cK
    caddc
    co
    cN
    cK
    caddc
    co
    cfz
    co
    #
    cB
    vk
    csu
    #
    @0
    cA
    @2
    vj
    vw
    vw
    cA
    nfcv
    vj
    @1
    cA
    nfcsb1v
    #
    vj
    @1
    cA
    csbeq1a
    #
    cbvsumi
    wph
    @3
    @4
    vj
    vk
    cv
    #
    cK
    cmin
    co
    #
    cA
    csb
    #
    vk
    csu
    @5
    wph
    @2
    @10
    vw
    vk
    cK
    cM
    cN
    fsumshftd.1
    fsumshftd.2
    fsumshftd.3
    wph
    vj
    cv
    #
    @0
    wcel
    #
    wa
    #
    cA
    cc
    wcel
    #
    wi
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    cc
    wcel
    #
    wi
    vj
    vw
    @16
    @17
    vj
    @16
    vj
    nfv
    vj
    @2
    cc
    @6
    nfel1
    nfim
    vj
    vw
    weq
    #
    @13
    @16
    @14
    @17
    @18
    @12
    @15
    wph
    @11
    @1
    @0
    eleq1
    anbi2d
    @18
    cA
    @2
    cc
    @7
    eleq1d
    imbi12d
    fsumshftd.4
    chvar
    vj
    @1
    @9
    cA
    csbeq1
    fsumshft
    wph
    @4
    @10
    cB
    vk
    wph
    vj
    @9
    cA
    cB
    cvv
    wph
    @8
    cK
    cmin
    ovexd
    fsumshftd.5
    csbied
    sumeq2sdv
    eqtrd
    syl5eq
end
