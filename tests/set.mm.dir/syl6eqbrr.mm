include "eqcomd.mm"
include "syl6eqbr.mm"

theorem syl6eqbrr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl6eqbrr.1: |- ( ph -> B = A )
  assume syl6eqbrr.2: |- B R C


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cC
    cR
    wph
    cB
    cA
    syl6eqbrr.1
    eqcomd
    syl6eqbrr.2
    syl6eqbr
end
