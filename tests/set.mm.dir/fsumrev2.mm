include "cfz.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "c0.mm"
include "cc0.mm"
include "sum0.mm"
include "eqtr4i.mm"
include "sumeq1.mm"
include "3eqtr4a.mm"
include "adantl.mm"
include "wne.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "fzn0.mm"
include "wa.mm"
include "caddc.mm"
include "cmin.mm"
include "cz.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "zaddcld.mm"
include "cv.mm"
include "cc.mm"
include "adantlr.mm"
include "fsumrev.mm"
include "zcnd.mm"
include "pncand.mm"
include "pncan2d.mm"
include "oveq12d.mm"
include "sumeq1d.mm"
include "eqtrd.mm"
include "sylan2b.mm"
include "pm2.61dane.mm"

theorem fsumrev2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fsumrev2.1: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. CC )
  assume fsumrev2.2: |- ( j = ( ( M + N ) - k ) -> A = B )

  disjoint A k
  disjoint B j
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> sum_ j e. ( M ... N ) A = sum_ k e. ( M ... N ) B )

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
    #
    @0
    cB
    vk
    csu
    #
    wceq
    #
    @0
    c0
    @0
    c0
    wceq
    #
    @3
    wph
    @4
    c0
    cA
    vj
    csu
    #
    c0
    cB
    vk
    csu
    #
    @1
    @2
    @5
    cc0
    @6
    cA
    vj
    sum0
    cB
    vk
    sum0
    eqtr4i
    @0
    c0
    cA
    vj
    sumeq1
    @0
    c0
    cB
    vk
    sumeq1
    3eqtr4a
    adantl
    @0
    c0
    wne
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @3
    cM
    cN
    fzn0
    wph
    @7
    wa
    #
    @1
    cM
    cN
    caddc
    co
    #
    cN
    cmin
    co
    #
    @9
    cM
    cmin
    co
    #
    cfz
    co
    #
    cB
    vk
    csu
    @2
    @8
    cA
    cB
    vj
    vk
    @9
    cM
    cN
    @8
    cM
    cN
    @7
    cM
    cz
    wcel
    wph
    cM
    cN
    eluzel2
    adantl
    #
    @7
    cN
    cz
    wcel
    wph
    cM
    cN
    eluzelz
    adantl
    #
    zaddcld
    @13
    @14
    wph
    vj
    cv
    @0
    wcel
    cA
    cc
    wcel
    @7
    fsumrev2.1
    adantlr
    fsumrev2.2
    fsumrev
    @8
    @12
    @0
    cB
    vk
    @8
    @10
    cM
    @11
    cN
    cfz
    @8
    cM
    cN
    @8
    cM
    @13
    zcnd
    #
    @8
    cN
    @14
    zcnd
    #
    pncand
    @8
    cM
    cN
    @15
    @16
    pncan2d
    oveq12d
    sumeq1d
    eqtrd
    sylan2b
    pm2.61dane
end
