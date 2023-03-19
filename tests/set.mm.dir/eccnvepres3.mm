include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cdm.mm"
include "wcel.mm"
include "cec.mm"
include "resdmres.mm"
include "eceq2i.mm"
include "eccnvepres2.mm"
include "syl5eqr.mm"

theorem eccnvepres3
  let cA: class A
  let cB: class B


  assert |- ( B e. dom ( `' _E |` A ) -> [ B ] ( `' _E |` A ) = B )

  proof
    cB
    cep
    ccnv
    #
    cA
    cres
    #
    cdm
    #
    wcel
    cB
    @1
    cec
    cB
    @0
    @2
    cres
    #
    cec
    cB
    @3
    @1
    cB
    @0
    cA
    resdmres
    eceq2i
    @2
    cB
    eccnvepres2
    syl5eqr
end
