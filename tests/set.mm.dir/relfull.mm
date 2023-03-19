include "cful.mm"
include "co.mm"
include "cfunc.mm"
include "wss.mm"
include "wrel.mm"
include "fullfunc.mm"
include "relfunc.mm"
include "relss.mm"
include "mp2.mm"

theorem relfull
  let cC: class C
  let cD: class D


  assert |- Rel ( C Full D )

  proof
    cC
    cD
    cful
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
    fullfunc
    cC
    cD
    relfunc
    @0
    @1
    relss
    mp2
end
