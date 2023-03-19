include "cop.mm"
include "cun.mm"
include "wcel.mm"
include "wo.mm"
include "wbr.mm"
include "elun.mm"
include "df-br.mm"
include "orbi12i.mm"
include "3bitr4i.mm"

theorem brun
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( A ( R u. S ) B <-> ( A R B \/ A S B ) )

  proof
    cA
    cB
    cop
    #
    cR
    cS
    cun
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
    wo
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
    wo
    @0
    cR
    cS
    elun
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
    orbi12i
    3bitr4i
end
