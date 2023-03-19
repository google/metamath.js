include "wceq.mm"
include "cima.mm"
include "imaeq1.mm"
include "syl.mm"

theorem imaeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume imaeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A " C ) = ( B " C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cima
    cB
    cC
    cima
    wceq
    imaeq1d.1
    cA
    cB
    cC
    imaeq1
    syl
end
