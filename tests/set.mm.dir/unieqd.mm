include "wceq.mm"
include "cuni.mm"
include "unieq.mm"
include "syl.mm"

theorem unieqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume unieqd.1: |- ( ph -> A = B )


  assert |- ( ph -> U. A = U. B )

  proof
    wph
    cA
    cB
    wceq
    cA
    cuni
    cB
    cuni
    wceq
    unieqd.1
    cA
    cB
    unieq
    syl
end
