include "wbr.mm"
include "breq1d.mm"
include "mpbird.mm"

theorem eqbrtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume eqbrtrd.1: |- ( ph -> A = B )
  assume eqbrtrd.2: |- ( ph -> B R C )


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
    eqbrtrd.2
    wph
    cA
    cB
    cC
    cR
    eqbrtrd.1
    breq1d
    mpbird
end
