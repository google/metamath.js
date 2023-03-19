include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "cec.mm"
include "eccnvep.mm"
include "eqeqan12d.mm"

theorem extep
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( [ A ] `' _E = [ B ] `' _E <-> A = B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    cA
    cep
    ccnv
    #
    cec
    cA
    cB
    @0
    cec
    cB
    cA
    cV
    eccnvep
    cB
    cW
    eccnvep
    eqeqan12d
end
