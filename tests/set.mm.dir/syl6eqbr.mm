include "wbr.mm"
include "breq1d.mm"
include "mpbiri.mm"

theorem syl6eqbr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl6eqbr.1: |- ( ph -> A = B )
  assume syl6eqbr.2: |- B R C


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cC
    cR
    wbr
    cB
    cC
    cR
    wbr
    syl6eqbr.2
    wph
    cA
    cB
    cC
    cR
    syl6eqbr.1
    breq1d
    mpbiri
end
