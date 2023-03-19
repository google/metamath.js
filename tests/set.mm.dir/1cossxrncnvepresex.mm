include "wcel.mm"
include "wa.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cxrn.mm"
include "cvv.mm"
include "ccoss.mm"
include "xrncnvepresex.mm"
include "cossex.mm"
include "syl.mm"

theorem 1cossxrncnvepresex
  let cA: class A
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ R e. W ) -> ,~ ( R |X. ( `' _E |` A ) ) e. _V )

  proof
    cA
    cV
    wcel
    cR
    cW
    wcel
    wa
    cR
    cep
    ccnv
    cA
    cres
    cxrn
    #
    cvv
    wcel
    @0
    ccoss
    cvv
    wcel
    cA
    cR
    cV
    cW
    xrncnvepresex
    @0
    cvv
    cossex
    syl
end
