include "cpr.mm"
include "nelpri.mm"
include "nelir.mm"

theorem prneli
  let cA: class A
  let cB: class B
  let cC: class C
  assume prneli.1: |- A =/= B
  assume prneli.2: |- A =/= C


  assert |- A e/ { B , C }

  proof
    cA
    cB
    cC
    cpr
    cA
    cB
    cC
    prneli.1
    prneli.2
    nelpri
    nelir
end
