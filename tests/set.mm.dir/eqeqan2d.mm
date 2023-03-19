include "wceq.mm"
include "wb.mm"
include "eqeq12.mm"
include "sylan2.mm"

theorem eqeqan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eqeqan2d.1: |- ( ph -> C = D )


  assert |- ( ( A = B /\ ph ) -> ( A = C <-> B = D ) )

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
    eqeqan2d.1
    cA
    cB
    cC
    cD
    eqeq12
    sylan2
end
