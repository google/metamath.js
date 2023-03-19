include "eqcomd.mm"
include "syl6eqss.mm"

theorem syl6eqssr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6eqssr.1: |- ( ph -> B = A )
  assume syl6eqssr.2: |- B C_ C


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    wph
    cB
    cA
    syl6eqssr.1
    eqcomd
    syl6eqssr.2
    syl6eqss
end
