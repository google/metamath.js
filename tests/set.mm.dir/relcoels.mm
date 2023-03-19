include "ccoels.mm"
include "wrel.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "ccoss.mm"
include "relcoss.mm"
include "df-coels.mm"
include "releqi.mm"
include "mpbir.mm"

theorem relcoels
  let cA: class A


  assert |- Rel ~ A

  proof
    cA
    ccoels
    #
    wrel
    cep
    ccnv
    cA
    cres
    #
    ccoss
    #
    wrel
    @1
    relcoss
    @0
    @2
    cA
    df-coels
    releqi
    mpbir
end
