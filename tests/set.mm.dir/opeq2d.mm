include "wceq.mm"
include "cop.mm"
include "opeq2.mm"
include "syl.mm"

theorem opeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume opeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> <. C , A >. = <. C , B >. )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cop
    cC
    cB
    cop
    wceq
    opeq1d.1
    cA
    cB
    cC
    opeq2
    syl
end
