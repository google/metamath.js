include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "brinxp2ALTV.mm"
include "df-br.mm"
include "anbi2i.mm"
include "3bitr3i.mm"

theorem opelinxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( <. C , D >. e. ( R i^i ( A X. B ) ) <-> ( ( C e. A /\ D e. B ) /\ <. C , D >. e. R ) )

  proof
    cC
    cD
    cR
    cA
    cB
    cxp
    cin
    #
    wbr
    cC
    cA
    wcel
    cD
    cB
    wcel
    wa
    #
    cC
    cD
    cR
    wbr
    #
    wa
    cC
    cD
    cop
    #
    @0
    wcel
    @1
    @3
    cR
    wcel
    #
    wa
    cA
    cB
    cC
    cD
    cR
    brinxp2ALTV
    cC
    cD
    @0
    df-br
    @2
    @4
    @1
    cC
    cD
    cR
    df-br
    anbi2i
    3bitr3i
end
