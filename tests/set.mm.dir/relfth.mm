include "cfth.mm"
include "co.mm"
include "cfunc.mm"
include "wss.mm"
include "wrel.mm"
include "fthfunc.mm"
include "relfunc.mm"
include "relss.mm"
include "mp2.mm"

theorem relfth
  let cC: class C
  let cD: class D


  assert |- Rel ( C Faith D )

  proof
    cC
    cD
    cfth
    co
    #
    cC
    cD
    cfunc
    co
    #
    wss
    @1
    wrel
    @0
    wrel
    cC
    cD
    fthfunc
    cC
    cD
    relfunc
    @0
    @1
    relss
    mp2
end
