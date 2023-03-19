include "wcel.mm"
include "ccat.mm"
include "ccid.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "cidfu.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqid.mm"
include "catccatid.mm"
include "simpld.mm"

theorem catccat
  let cC: class C
  let cU: class U
  let cV: class V
  let vx: setvar x
  assume catccat.c: |- C = ( CatCat ` U )


  assert |- ( U e. V -> C e. Cat )

  proof
    cU
    cV
    wcel
    cC
    ccat
    wcel
    cC
    ccid
    cfv
    vx
    cC
    cbs
    cfv
    #
    vx
    cv
    cidfu
    cfv
    cmpt
    wceq
    vx
    @0
    cC
    cU
    cV
    catccat.c
    @0
    eqid
    catccatid
    simpld
end
