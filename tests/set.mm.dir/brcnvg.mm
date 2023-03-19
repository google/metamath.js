include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "ccnv.mm"
include "wbr.mm"
include "opelcnvg.mm"
include "df-br.mm"
include "3bitr4g.mm"

theorem brcnvg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( A e. C /\ B e. D ) -> ( A `' R B <-> B R A ) )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    cA
    cB
    cop
    cR
    ccnv
    #
    wcel
    cB
    cA
    cop
    cR
    wcel
    cA
    cB
    @0
    wbr
    cB
    cA
    cR
    wbr
    cA
    cB
    cC
    cD
    cR
    opelcnvg
    cA
    cB
    @0
    df-br
    cB
    cA
    cR
    df-br
    3bitr4g
end
