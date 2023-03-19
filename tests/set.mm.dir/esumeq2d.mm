include "eqidd.mm"
include "wceq.mm"
include "r19.21bi.mm"
include "esumeq12dvaf.mm"

theorem esumeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume esumeq2d.0: |- F/ k ph
  assume esumeq2d.1: |- ( ph -> A. k e. A B = C )


  assert |- ( ph -> sum* k e. A B = sum* k e. A C )

  proof
    wph
    cA
    cA
    cB
    cC
    vk
    esumeq2d.0
    wph
    cA
    eqidd
    wph
    cB
    cC
    wceq
    vk
    cA
    esumeq2d.1
    r19.21bi
    esumeq12dvaf
end
