include "wbr.mm"
include "breq1d.mm"
include "mtbird.mm"

theorem eqnbrtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume eqnbrtrd.1: |- ( ph -> A = B )
  assume eqnbrtrd.2: |- ( ph -> -. B R C )


  assert |- ( ph -> -. A R C )

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
    eqnbrtrd.2
    wph
    cA
    cB
    cC
    cR
    eqnbrtrd.1
    breq1d
    mtbird
end
