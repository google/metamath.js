include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "cdif.mm"
include "wn.mm"
include "wbr.mm"
include "opelvvdif.mm"
include "df-br.mm"
include "notbii.mm"
include "3bitr4g.mm"

theorem brvvdif
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ( ( _V X. _V ) \ R ) B <-> -. A R B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cop
    #
    cvv
    cvv
    cxp
    cR
    cdif
    #
    wcel
    @0
    cR
    wcel
    #
    wn
    cA
    cB
    @1
    wbr
    cA
    cB
    cR
    wbr
    #
    wn
    cA
    cB
    cR
    cV
    cW
    opelvvdif
    cA
    cB
    @1
    df-br
    @3
    @2
    cA
    cB
    cR
    df-br
    notbii
    3bitr4g
end
