include "syl6eqss.mm"

theorem bnj1262
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume bnj1262.1: |- A C_ B
  assume bnj1262.2: |- ( ph -> C = A )


  assert |- ( ph -> C C_ B )

  proof
    wph
    cC
    cA
    cB
    bnj1262.2
    bnj1262.1
    syl6eqss
end
