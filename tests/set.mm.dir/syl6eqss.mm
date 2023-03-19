include "wss.mm"
include "a1i.mm"
include "eqsstrd.mm"

theorem syl6eqss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6eqss.1: |- ( ph -> A = B )
  assume syl6eqss.2: |- B C_ C


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    syl6eqss.1
    cB
    cC
    wss
    wph
    syl6eqss.2
    a1i
    eqsstrd
end
