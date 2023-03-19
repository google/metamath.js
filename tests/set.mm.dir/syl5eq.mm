include "wceq.mm"
include "a1i.mm"
include "eqtrd.mm"

theorem syl5eq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eq.1: |- A = B
  assume syl5eq.2: |- ( ph -> B = C )


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cB
    cC
    cA
    cB
    wceq
    wph
    syl5eq.1
    a1i
    syl5eq.2
    eqtrd
end
