include "csu.mm"
include "sumeq1d.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"

theorem sumeq12rdv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume sumeq12rdv.1: |- ( ph -> A = B )
  assume sumeq12rdv.2: |- ( ( ph /\ k e. B ) -> C = D )

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
    cB
    cC
    vk
    csu
    cB
    cD
    vk
    csu
    wph
    cA
    cB
    cC
    vk
    sumeq12rdv.1
    sumeq1d
    wph
    cB
    cC
    cD
    vk
    sumeq12rdv.2
    sumeq2dv
    eqtrd
end
