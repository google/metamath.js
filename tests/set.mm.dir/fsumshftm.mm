include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cv.mm"
include "csb.mm"
include "cmin.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "cneg.mm"
include "caddc.mm"
include "znegcld.mm"
include "cc.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "wceq.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "csbeq1.mm"
include "fsumshft.mm"
include "zcnd.mm"
include "negsubd.mm"
include "oveq12d.mm"
include "sumeq1d.mm"
include "wa.mm"
include "elfzelz.mm"
include "subneg.mm"
include "syl2anr.mm"
include "csbeq1d.mm"
include "ovex.mm"
include "csbie.mm"
include "syl6eq.mm"
include "sumeq2dv.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem fsumshftm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume fsumrev.1: |- ( ph -> K e. ZZ )
  assume fsumrev.2: |- ( ph -> M e. ZZ )
  assume fsumrev.3: |- ( ph -> N e. ZZ )
  assume fsumrev.4: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. CC )
  assume fsumshftm.5: |- ( j = ( k + K ) -> A = B )

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
  disjoint k m
  disjoint A m
  disjoint j m
  disjoint K m
  disjoint M m
  disjoint N m
  disjoint m ph
  assert |- ( ph -> sum_ j e. ( M ... N ) A = sum_ k e. ( ( M - K ) ... ( N - K ) ) B )

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
    vm
    cv
    #
    cA
    csb
    #
    vm
    csu
    #
    cM
    cK
    cmin
    co
    #
    cN
    cK
    cmin
    co
    #
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
    vm
    vm
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
    cM
    cK
    cneg
    #
    caddc
    co
    #
    cN
    @10
    caddc
    co
    #
    cfz
    co
    #
    vj
    vk
    cv
    #
    @10
    cmin
    co
    #
    cA
    csb
    #
    vk
    csu
    @6
    @16
    vk
    csu
    @7
    wph
    @2
    @16
    vm
    vk
    @10
    cM
    cN
    wph
    cK
    fsumrev.1
    znegcld
    fsumrev.2
    fsumrev.3
    wph
    cA
    cc
    wcel
    #
    vj
    @0
    wral
    @1
    @0
    wcel
    @2
    cc
    wcel
    #
    wph
    @17
    vj
    @0
    fsumrev.4
    ralrimiva
    @17
    @18
    vj
    @1
    @0
    vj
    @2
    cc
    @8
    nfel1
    vj
    cv
    @1
    wceq
    cA
    @2
    cc
    @9
    eleq1d
    rspc
    mpan9
    vj
    @1
    @15
    cA
    csbeq1
    fsumshft
    wph
    @13
    @6
    @16
    vk
    wph
    @11
    @4
    @12
    @5
    cfz
    wph
    cM
    cK
    wph
    cM
    fsumrev.2
    zcnd
    wph
    cK
    fsumrev.1
    zcnd
    #
    negsubd
    wph
    cN
    cK
    wph
    cN
    fsumrev.3
    zcnd
    @19
    negsubd
    oveq12d
    sumeq1d
    wph
    @6
    @16
    cB
    vk
    wph
    @14
    @6
    wcel
    #
    wa
    #
    @16
    vj
    @14
    cK
    caddc
    co
    #
    cA
    csb
    cB
    @21
    vj
    @15
    @22
    cA
    @20
    @14
    cc
    wcel
    cK
    cc
    wcel
    @15
    @22
    wceq
    wph
    @20
    @14
    @14
    @4
    @5
    elfzelz
    zcnd
    @19
    @14
    cK
    subneg
    syl2anr
    csbeq1d
    vj
    @22
    cA
    cB
    @14
    cK
    caddc
    ovex
    fsumshftm.5
    csbie
    syl6eq
    sumeq2dv
    3eqtrd
    syl5eq
end
