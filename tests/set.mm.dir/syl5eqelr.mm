include "eqcomi.mm"
include "syl5eqel.mm"

theorem syl5eqelr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eqelr.1: |- B = A
  assume syl5eqelr.2: |- ( ph -> B e. C )


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    cB
    cA
    syl5eqelr.1
    eqcomi
    syl5eqelr.2
    syl5eqel
end
