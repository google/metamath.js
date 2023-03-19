include "cfzo.mm"
include "co.mm"
include "csu.mm"
include "caddc.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzelz.mm"
include "syl.mm"
include "fzoval.mm"
include "sumeq1d.mm"
include "oveq1d.mm"
include "fsumm1.mm"
include "fzval3.mm"
include "3eqtr2rd.mm"

theorem fzosump1
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
  assert |- ( ph -> sum_ k e. ( M ..^ ( N + 1 ) ) A = ( sum_ k e. ( M ..^ N ) A + B ) )

  proof
    wph
    cM
    cN
    cfzo
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
    c1
    cmin
    co
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
    cM
    cN
    c1
    caddc
    co
    cfzo
    co
    #
    cA
    vk
    csu
    wph
    @1
    @3
    cB
    caddc
    wph
    @0
    @2
    cA
    vk
    wph
    cN
    cz
    wcel
    #
    @0
    @2
    wceq
    wph
    cN
    cM
    cuz
    cfv
    wcel
    @6
    fsumm1.1
    cM
    cN
    eluzelz
    syl
    #
    cM
    cN
    fzoval
    syl
    sumeq1d
    oveq1d
    wph
    cA
    cB
    vk
    cM
    cN
    fsumm1.1
    fsumm1.2
    fsumm1.3
    fsumm1
    wph
    @4
    @5
    cA
    vk
    wph
    @6
    @4
    @5
    wceq
    @7
    cM
    cN
    fzval3
    syl
    sumeq1d
    3eqtr2rd
end
