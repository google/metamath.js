include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cvv.mm"
include "ccoss.mm"
include "cnvepresex.mm"
include "cossex.mm"
include "syl.mm"

theorem 1cosscnvepresex
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ,~ ( `' _E |` A ) e. _V )

  proof
    cA
    cV
    wcel
    cep
    ccnv
    cA
    cres
    #
    cvv
    wcel
    @0
    ccoss
    cvv
    wcel
    cA
    cV
    cnvepresex
    @0
    cvv
    cossex
    syl
end
