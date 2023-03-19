include "wcel.mm"
include "a1i.mm"
include "eqeltrd.mm"

theorem syl6eqel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6eqel.1: |- ( ph -> A = B )
  assume syl6eqel.2: |- B e. C


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    syl6eqel.1
    cB
    cC
    wcel
    wph
    syl6eqel.2
    a1i
    eqeltrd
end
