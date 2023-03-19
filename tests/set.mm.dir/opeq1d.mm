include "wceq.mm"
include "cop.mm"
include "opeq1.mm"
include "syl.mm"

theorem opeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume opeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> <. A , C >. = <. B , C >. )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cop
    cB
    cC
    cop
    wceq
    opeq1d.1
    cA
    cB
    cC
    opeq1
    syl
end
