include "wceq.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "eleq2.mm"
include "df-br.mm"
include "3bitr4g.mm"

theorem breq
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( R = S -> ( A R B <-> A S B ) )

  proof
    cR
    cS
    wceq
    cA
    cB
    cop
    #
    cR
    wcel
    @0
    cS
    wcel
    cA
    cB
    cR
    wbr
    cA
    cB
    cS
    wbr
    cR
    cS
    @0
    eleq2
    cA
    cB
    cR
    df-br
    cA
    cB
    cS
    df-br
    3bitr4g
end
