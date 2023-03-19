include "cprod.mm"
include "prodeq2dv.mm"
include "prodeq1d.mm"
include "eqtrd.mm"

theorem prodeq12dv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume prodeq12dv.1: |- ( ph -> A = B )
  assume prodeq12dv.2: |- ( ( ph /\ k e. A ) -> C = D )

  disjoint A k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> prod_ k e. A C = prod_ k e. B D )

  proof
    wph
    cA
    cC
    vk
    cprod
    cA
    cD
    vk
    cprod
    cB
    cD
    vk
    cprod
    wph
    cA
    cC
    cD
    vk
    prodeq12dv.2
    prodeq2dv
    wph
    cA
    cB
    cD
    vk
    prodeq12dv.1
    prodeq1d
    eqtrd
end
