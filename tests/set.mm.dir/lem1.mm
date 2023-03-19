include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "ltm1.mm"
include "wi.mm"
include "peano2rem.mm"
include "ltle.mm"
include "mpancom.mm"
include "mpd.mm"

theorem lem1
  let cA: class A


  assert |- ( A e. RR -> ( A - 1 ) <_ A )

  proof
    cA
    cr
    wcel
    #
    cA
    c1
    cmin
    co
    #
    cA
    clt
    wbr
    #
    @1
    cA
    cle
    wbr
    #
    cA
    ltm1
    @1
    cr
    wcel
    @0
    @2
    @3
    wi
    cA
    peano2rem
    @1
    cA
    ltle
    mpancom
    mpd
end
