include "wceq.mm"
include "cin.mm"
include "ineq2.mm"
include "syl.mm"

theorem ineq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ineq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C i^i A ) = ( C i^i B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cin
    cC
    cB
    cin
    wceq
    ineq1d.1
    cA
    cB
    cC
    ineq2
    syl
end
