include "wceq.mm"
include "wb.mm"
include "eqeq12.mm"
include "sylan.mm"

theorem eqeqan1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eqeqan1d.1: |- ( ph -> A = B )


  assert |- ( ( ph /\ C = D ) -> ( A = C <-> B = D ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    wceq
    cB
    cD
    wceq
    wb
    eqeqan1d.1
    cA
    cB
    cC
    cD
    eqeq12
    sylan
end
