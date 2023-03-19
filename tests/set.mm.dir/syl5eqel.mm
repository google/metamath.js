include "wceq.mm"
include "a1i.mm"
include "eqeltrd.mm"

theorem syl5eqel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eqel.1: |- A = B
  assume syl5eqel.2: |- ( ph -> B e. C )


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    cA
    cB
    wceq
    wph
    syl5eqel.1
    a1i
    syl5eqel.2
    eqeltrd
end
