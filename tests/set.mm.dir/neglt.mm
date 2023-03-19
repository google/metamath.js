include "crp.mm"
include "wcel.mm"
include "cneg.mm"
include "cc0.mm"
include "rpre.mm"
include "renegcld.mm"
include "0red.mm"
include "clt.mm"
include "wbr.mm"
include "rpgt0.mm"
include "lt0neg2d.mm"
include "mpbid.mm"
include "lttrd.mm"

theorem neglt
  let cA: class A


  assert |- ( A e. RR+ -> -u A < A )

  proof
    cA
    crp
    wcel
    #
    cA
    cneg
    #
    cc0
    cA
    @0
    cA
    cA
    rpre
    #
    renegcld
    @0
    0red
    @2
    @0
    cc0
    cA
    clt
    wbr
    @1
    cc0
    clt
    wbr
    cA
    rpgt0
    #
    @0
    cA
    @2
    lt0neg2d
    mpbid
    @3
    lttrd
end
