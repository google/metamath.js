include "cprod.mm"
include "prodeq1d.mm"
include "prodeq2dv.mm"
include "eqtrd.mm"

theorem prodeq12rdv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume prodeq12rdv.1: |- ( ph -> A = B )
  assume prodeq12rdv.2: |- ( ( ph /\ k e. B ) -> C = D )

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
    cB
    cC
    vk
    cprod
    cB
    cD
    vk
    cprod
    wph
    cA
    cB
    cC
    vk
    prodeq12rdv.1
    prodeq1d
    wph
    cB
    cC
    cD
    vk
    prodeq12rdv.2
    prodeq2dv
    eqtrd
end
