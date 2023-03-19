include "cep.mm"
include "ccnv.mm"
include "wbr.mm"
include "wcel.mm"
include "rele.mm"
include "relbrcnv.mm"
include "epelg.mm"
include "syl5bb.mm"

theorem brcnvep
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A `' _E B <-> B e. A ) )

  proof
    cA
    cB
    cep
    ccnv
    wbr
    cB
    cA
    cep
    wbr
    cA
    cV
    wcel
    cB
    cA
    wcel
    cA
    cB
    cep
    rele
    relbrcnv
    cB
    cA
    cV
    epelg
    syl5bb
end
