include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "csu.mm"
include "cmin.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "peano2uz.mm"
include "syl.mm"
include "fsumm1.mm"
include "cc.mm"
include "wceq.mm"
include "cz.mm"
include "eluzelz.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem fsump1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fsump1.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsump1.2: |- ( ( ph /\ k e. ( M ... ( N + 1 ) ) ) -> A e. CC )
  assume fsump1.3: |- ( k = ( N + 1 ) -> A = B )

  disjoint B k
  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> sum_ k e. ( M ... ( N + 1 ) ) A = ( sum_ k e. ( M ... N ) A + B ) )

  proof
    wph
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    cA
    vk
    csu
    cM
    @0
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
    cB
    caddc
    co
    cM
    cN
    cfz
    co
    #
    cA
    vk
    csu
    #
    cB
    caddc
    co
    wph
    cA
    cB
    vk
    cM
    @0
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @0
    @6
    wcel
    fsump1.1
    cM
    cN
    peano2uz
    syl
    fsump1.2
    fsump1.3
    fsumm1
    wph
    @3
    @5
    cB
    caddc
    wph
    @2
    @4
    cA
    vk
    wph
    @1
    cN
    cM
    cfz
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    @1
    cN
    wceq
    wph
    cN
    wph
    @7
    cN
    cz
    wcel
    fsump1.1
    cM
    cN
    eluzelz
    syl
    zcnd
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq1d
    eqtrd
end
