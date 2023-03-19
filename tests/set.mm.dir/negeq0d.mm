include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "cneg.mm"
include "wb.mm"
include "negeq0.mm"
include "syl.mm"

theorem negeq0d
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A = 0 <-> -u A = 0 ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wceq
    cA
    cneg
    cc0
    wceq
    wb
    negidd.1
    cA
    negeq0
    syl
end
