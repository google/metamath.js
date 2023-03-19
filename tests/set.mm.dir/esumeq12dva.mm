include "nfv.mm"
include "esumeq12dvaf.mm"

theorem esumeq12dva
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume esumeq12dva.1: |- ( ph -> A = B )
  assume esumeq12dva.2: |- ( ( ph /\ k e. A ) -> C = D )

  disjoint k ph
  assert |- ( ph -> sum* k e. A C = sum* k e. B D )

  proof
    wph
    cA
    cB
    cC
    cD
    vk
    wph
    vk
    nfv
    esumeq12dva.1
    esumeq12dva.2
    esumeq12dvaf
end
