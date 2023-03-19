include "wceq.mm"
include "cima.mm"
include "imaeq2.mm"
include "syl.mm"

theorem imaeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume imaeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C " A ) = ( C " B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cima
    cC
    cB
    cima
    wceq
    imaeq1d.1
    cA
    cB
    cC
    imaeq2
    syl
end
