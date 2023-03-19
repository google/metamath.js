include "c0.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "noel.mm"
include "df-br.mm"
include "mtbir.mm"

theorem br0
  let cA: class A
  let cB: class B


  assert |- -. A (/) B

  proof
    cA
    cB
    c0
    wbr
    cA
    cB
    cop
    #
    c0
    wcel
    @0
    noel
    cA
    cB
    c0
    df-br
    mtbir
end
