include "wceq.mm"
include "crn.mm"
include "rneq.mm"
include "syl.mm"

theorem rneqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rneqd.1: |- ( ph -> A = B )


  assert |- ( ph -> ran A = ran B )

  proof
    wph
    cA
    cB
    wceq
    cA
    crn
    cB
    crn
    wceq
    rneqd.1
    cA
    cB
    rneq
    syl
end
