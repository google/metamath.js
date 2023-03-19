include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "wbr.mm"
include "cop.mm"
include "cxrn.mm"
include "csn.mm"
include "brin2.mm"
include "wceq.mm"
include "opidg.mm"
include "adantl.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem brin3
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ( R i^i S ) B <-> A ( R |X. S ) { { B } } ) )

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
    #
    cA
    cB
    cR
    cS
    cin
    wbr
    cA
    cB
    cB
    cop
    #
    cR
    cS
    cxrn
    #
    wbr
    cA
    cB
    csn
    csn
    #
    @4
    wbr
    cA
    cB
    cR
    cS
    cV
    cW
    brin2
    @2
    @3
    @5
    cA
    @4
    @1
    @3
    @5
    wceq
    @0
    cB
    cW
    opidg
    adantl
    breq2d
    bitrd
end
