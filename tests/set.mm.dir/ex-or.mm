include "c4.mm"
include "wceq.mm"
include "c2.mm"
include "c3.mm"
include "eqid.mm"
include "olci.mm"

theorem ex-or



  assert |- ( 2 = 3 \/ 4 = 4 )

  proof
    c4
    c4
    wceq
    c2
    c3
    wceq
    c4
    eqid
    olci
end
