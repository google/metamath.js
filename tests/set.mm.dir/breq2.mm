include "wceq.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "df-br.mm"
include "3bitr4g.mm"

theorem breq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( A = B -> ( C R A <-> C R B ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cop
    #
    cR
    wcel
    cC
    cB
    cop
    #
    cR
    wcel
    cC
    cA
    cR
    wbr
    cC
    cB
    cR
    wbr
    @0
    @1
    @2
    cR
    cA
    cB
    cC
    opeq2
    eleq1d
    cC
    cA
    cR
    df-br
    cC
    cB
    cR
    df-br
    3bitr4g
end
