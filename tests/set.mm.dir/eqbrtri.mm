include "wbr.mm"
include "breq1i.mm"
include "mpbir.mm"

theorem eqbrtri
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume eqbrtr.1: |- A = B
  assume eqbrtr.2: |- B R C


  assert |- A R C

  proof
    cA
    cC
    cR
    wbr
    cB
    cC
    cR
    wbr
    eqbrtr.2
    cA
    cB
    cC
    cR
    eqbrtr.1
    breq1i
    mpbir
end
