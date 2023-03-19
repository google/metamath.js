include "wceq.mm"
include "cin.mm"
include "ineq1.mm"
include "syl.mm"

theorem ineq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ineq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A i^i C ) = ( B i^i C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cin
    cB
    cC
    cin
    wceq
    ineq1d.1
    cA
    cB
    cC
    ineq1
    syl
end
