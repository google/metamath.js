include "wceq.mm"
include "eqcom.mm"
include "sylbi.mm"

theorem eqcoms
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume eqcoms.1: |- ( A = B -> ph )


  assert |- ( B = A -> ph )

  proof
    cB
    cA
    wceq
    cA
    cB
    wceq
    wph
    cB
    cA
    eqcom
    eqcoms.1
    sylbi
end
