include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "esumeq12dvaf.mm"

theorem esumeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume esumeq1d.0: |- F/ k ph
  assume esumeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> sum* k e. A C = sum* k e. B C )

  proof
    wph
    cA
    cB
    cC
    cC
    vk
    esumeq1d.0
    esumeq1d.1
    wph
    vk
    cv
    cA
    wcel
    wa
    cC
    eqidd
    esumeq12dvaf
end
