include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cxrn.mm"
include "wbr.mm"
include "cin.mm"
include "wb.mm"
include "brxrn.mm"
include "3anidm23.mm"
include "brin.mm"
include "syl6rbbr.mm"

theorem brin2
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ( R i^i S ) B <-> A ( R |X. S ) <. B , B >. ) )

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
    cB
    cB
    cop
    cR
    cS
    cxrn
    wbr
    #
    cA
    cB
    cR
    wbr
    cA
    cB
    cS
    wbr
    wa
    #
    cA
    cB
    cR
    cS
    cin
    wbr
    @0
    @1
    @2
    @3
    wb
    cA
    cB
    cB
    cR
    cS
    cV
    cW
    cW
    brxrn
    3anidm23
    cA
    cB
    cR
    cS
    brin
    syl6rbbr
end
