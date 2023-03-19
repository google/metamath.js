include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "cop.mm"
include "cec.mm"
include "wbr.mm"
include "wb.mm"
include "elimasng.mm"
include "ancoms.mm"
include "df-ec.mm"
include "eleq2i.mm"
include "df-br.mm"
include "3bitr4g.mm"

theorem elecg
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A e. [ B ] R <-> B R A ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cA
    cR
    cB
    csn
    cima
    #
    wcel
    #
    cB
    cA
    cop
    cR
    wcel
    #
    cA
    cB
    cR
    cec
    #
    wcel
    cB
    cA
    cR
    wbr
    @1
    @0
    @3
    @4
    wb
    cR
    cB
    cA
    cW
    cV
    elimasng
    ancoms
    @5
    @2
    cA
    cB
    cR
    df-ec
    eleq2i
    cB
    cA
    cR
    df-br
    3bitr4g
end
