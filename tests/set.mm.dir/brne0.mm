include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "df-br.mm"
include "ne0i.mm"
include "sylbi.mm"

theorem brne0
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A R B -> R =/= (/) )

  proof
    cA
    cB
    cR
    wbr
    cA
    cB
    cop
    #
    cR
    wcel
    cR
    c0
    wne
    cA
    cB
    cR
    df-br
    cR
    @0
    ne0i
    sylbi
end
