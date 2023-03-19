include "eqcomd.mm"
include "syl6eqel.mm"

theorem syl6eqelr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6eqelr.1: |- ( ph -> B = A )
  assume syl6eqelr.2: |- B e. C


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    wph
    cB
    cA
    syl6eqelr.1
    eqcomd
    syl6eqelr.2
    syl6eqel
end
