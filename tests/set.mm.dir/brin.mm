include "cop.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "elin.mm"
include "df-br.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem brin
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( A ( R i^i S ) B <-> ( A R B /\ A S B ) )

  proof
    cA
    cB
    cop
    #
    cR
    cS
    cin
    #
    wcel
    @0
    cR
    wcel
    #
    @0
    cS
    wcel
    #
    wa
    cA
    cB
    @1
    wbr
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cS
    wbr
    #
    wa
    @0
    cR
    cS
    elin
    cA
    cB
    @1
    df-br
    @4
    @2
    @5
    @3
    cA
    cB
    cR
    df-br
    cA
    cB
    cS
    df-br
    anbi12i
    3bitr4i
end
