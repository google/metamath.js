include "wceq.mm"
include "a1i.mm"
include "eqnetrrd.mm"

theorem syl5eqner
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eqner.1: |- B = A
  assume syl5eqner.2: |- ( ph -> B =/= C )


  assert |- ( ph -> A =/= C )

  proof
    wph
    cB
    cA
    cC
    cB
    cA
    wceq
    wph
    syl5eqner.1
    a1i
    syl5eqner.2
    eqnetrrd
end
