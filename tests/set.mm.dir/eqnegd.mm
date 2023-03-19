include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "cc0.mm"
include "wb.mm"
include "eqneg.mm"
include "syl.mm"

theorem eqnegd
  let wph: wff ph
  let cA: class A
  assume eqnegd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A = -u A <-> A = 0 ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cA
    cneg
    wceq
    cA
    cc0
    wceq
    wb
    eqnegd.1
    cA
    eqneg
    syl
end
