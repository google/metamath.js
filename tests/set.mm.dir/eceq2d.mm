include "wceq.mm"
include "cec.mm"
include "eceq2.mm"
include "syl.mm"

theorem eceq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eceq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> [ C ] A = [ C ] B )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cec
    cC
    cB
    cec
    wceq
    eceq2d.1
    cA
    cB
    cC
    eceq2
    syl
end
