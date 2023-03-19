include "c1.mm"
include "cc0.mm"
include "c2.mm"
include "cdc.mm"
include "1nn0.mm"
include "0nn0.mm"
include "eqid.mm"
include "1p1e2.mm"
include "00id.mm"
include "decadd.mm"

theorem 10p10e20



  assert |- ( ; 1 0 + ; 1 0 ) = ; 2 0

  proof
    c1
    cc0
    c1
    cc0
    c2
    cc0
    c1
    cc0
    cdc
    #
    @0
    1nn0
    0nn0
    1nn0
    0nn0
    @0
    eqid
    #
    @1
    1p1e2
    00id
    decadd
end
