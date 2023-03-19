include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "sqneg.mm"
include "ax-mp.mm"
include "sq1.mm"
include "eqtri.mm"

theorem neg1sqe1



  assert |- ( -u 1 ^ 2 ) = 1

  proof
    c1
    cneg
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    c1
    c1
    cc
    wcel
    @0
    @1
    wceq
    ax-1cn
    c1
    sqneg
    ax-mp
    sq1
    eqtri
end
