include "cssr.mm"
include "ccnv.mm"
include "wbr.mm"
include "wcel.mm"
include "wss.mm"
include "relssr.mm"
include "relbrcnv.mm"
include "brssr.mm"
include "syl5bb.mm"

theorem brcnvssr
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A `' _S B <-> B C_ A ) )

  proof
    cA
    cB
    cssr
    ccnv
    wbr
    cB
    cA
    cssr
    wbr
    cA
    cV
    wcel
    cB
    cA
    wss
    cA
    cB
    cssr
    relssr
    relbrcnv
    cB
    cA
    cV
    brssr
    syl5bb
end
