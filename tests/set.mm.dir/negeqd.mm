include "wceq.mm"
include "cneg.mm"
include "negeq.mm"
include "syl.mm"

theorem negeqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> -u A = -u B )

  proof
    wph
    cA
    cB
    wceq
    cA
    cneg
    cB
    cneg
    wceq
    negeqd.1
    cA
    cB
    negeq
    syl
end
