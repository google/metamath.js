include "eqcomd.mm"
include "eqbrtrd.mm"

theorem eqbrtrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume eqbrtrrd.1: |- ( ph -> A = B )
  assume eqbrtrrd.2: |- ( ph -> A R C )


  assert |- ( ph -> B R C )

  proof
    wph
    cB
    cA
    cC
    cR
    wph
    cA
    cB
    eqbrtrrd.1
    eqcomd
    eqbrtrrd.2
    eqbrtrd
end
