include "wceq.mm"
include "cxne.mm"
include "xnegeq.mm"
include "syl.mm"

theorem xnegeqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xnegeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> -e A = -e B )

  proof
    wph
    cA
    cB
    wceq
    cA
    cxne
    cB
    cxne
    wceq
    xnegeqd.1
    cA
    cB
    xnegeq
    syl
end
