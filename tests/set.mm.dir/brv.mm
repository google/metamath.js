include "cvv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "opex.mm"
include "df-br.mm"
include "mpbir.mm"

theorem brv
  let cA: class A
  let cB: class B


  assert |- A _V B

  proof
    cA
    cB
    cvv
    wbr
    cA
    cB
    cop
    cvv
    wcel
    cA
    cB
    opex
    cA
    cB
    cvv
    df-br
    mpbir
end
