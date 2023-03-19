include "eqcomi.mm"
include "syl5eq.mm"

theorem syl5eqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eqr.1: |- B = A
  assume syl5eqr.2: |- ( ph -> B = C )


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cB
    cC
    cB
    cA
    syl5eqr.1
    eqcomi
    syl5eqr.2
    syl5eq
end
