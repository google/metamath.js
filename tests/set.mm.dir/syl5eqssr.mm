include "eqcomi.mm"
include "syl5eqss.mm"

theorem syl5eqssr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eqssr.1: |- B = A
  assume syl5eqssr.2: |- ( ph -> B C_ C )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    cB
    cA
    syl5eqssr.1
    eqcomi
    syl5eqssr.2
    syl5eqss
end
