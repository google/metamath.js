include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cec.mm"
include "ecres2.mm"
include "eccnvep.mm"
include "eqtrd.mm"

theorem eccnvepres2
  let cA: class A
  let cB: class B


  assert |- ( B e. A -> [ B ] ( `' _E |` A ) = B )

  proof
    cB
    cA
    wcel
    cB
    cep
    ccnv
    #
    cA
    cres
    cec
    cB
    @0
    cec
    cB
    cA
    cB
    @0
    ecres2
    cB
    cA
    eccnvep
    eqtrd
end
