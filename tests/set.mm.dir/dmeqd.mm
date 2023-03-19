include "wceq.mm"
include "cdm.mm"
include "dmeq.mm"
include "syl.mm"

theorem dmeqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume dmeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> dom A = dom B )

  proof
    wph
    cA
    cB
    wceq
    cA
    cdm
    cB
    cdm
    wceq
    dmeqd.1
    cA
    cB
    dmeq
    syl
end
