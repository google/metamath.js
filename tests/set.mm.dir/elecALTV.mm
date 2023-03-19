include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "cop.mm"
include "cec.mm"
include "wbr.mm"
include "elimasng.mm"
include "df-ec.mm"
include "eleq2i.mm"
include "df-br.mm"
include "3bitr4g.mm"

theorem elecALTV
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( B e. [ A ] R <-> A R B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cB
    cR
    cA
    csn
    cima
    #
    wcel
    cA
    cB
    cop
    cR
    wcel
    cB
    cA
    cR
    cec
    #
    wcel
    cA
    cB
    cR
    wbr
    cR
    cA
    cB
    cV
    cW
    elimasng
    @1
    @0
    cB
    cA
    cR
    df-ec
    eleq2i
    cA
    cB
    cR
    df-br
    3bitr4g
end
