include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "esumeq12dva.mm"

theorem esumeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume esumeq12d.1: |- ( ph -> A = B )
  assume esumeq12d.2: |- ( ph -> C = D )

  disjoint k ph
  assert |- ( ph -> sum* k e. A C = sum* k e. B D )

  proof
    wph
    cA
    cB
    cC
    cD
    vk
    esumeq12d.1
    wph
    cC
    cD
    wceq
    vk
    cv
    cA
    wcel
    esumeq12d.2
    adantr
    esumeq12dva
end
