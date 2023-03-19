include "csu.mm"
include "sumeq2dv.mm"
include "sumeq1d.mm"
include "eqtrd.mm"

theorem sumeq12dv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume sumeq12dv.1: |- ( ph -> A = B )
  assume sumeq12dv.2: |- ( ( ph /\ k e. A ) -> C = D )

  disjoint A k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A C = sum_ k e. B D )

  proof
    wph
    cA
    cC
    vk
    csu
    cA
    cD
    vk
    csu
    cB
    cD
    vk
    csu
    wph
    cA
    cC
    cD
    vk
    sumeq12dv.2
    sumeq2dv
    wph
    cA
    cB
    cD
    vk
    sumeq12dv.1
    sumeq1d
    eqtrd
end
