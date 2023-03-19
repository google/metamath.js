include "wss.mm"
include "cuni.mm"
include "uniss.mm"
include "syl.mm"

theorem unissd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume unissd.1: |- ( ph -> A C_ B )


  assert |- ( ph -> U. A C_ U. B )

  proof
    wph
    cA
    cB
    wss
    cA
    cuni
    cB
    cuni
    wss
    unissd.1
    cA
    cB
    uniss
    syl
end
