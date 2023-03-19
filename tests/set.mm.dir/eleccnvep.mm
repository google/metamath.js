include "cep.mm"
include "ccnv.mm"
include "cec.mm"
include "wcel.mm"
include "wbr.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "relelec.mm"
include "ax-mp.mm"
include "brcnvep.mm"
include "syl5bb.mm"

theorem eleccnvep
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( B e. [ A ] `' _E <-> B e. A ) )

  proof
    cB
    cA
    cep
    ccnv
    #
    cec
    wcel
    #
    cA
    cB
    @0
    wbr
    #
    cA
    cV
    wcel
    cB
    cA
    wcel
    @0
    wrel
    @1
    @2
    wb
    cep
    relcnv
    cB
    cA
    @0
    relelec
    ax-mp
    cA
    cB
    cV
    brcnvep
    syl5bb
end
