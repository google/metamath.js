include "c2.mm"
include "wceq.mm"
include "c3.mm"
include "eqid.mm"
include "pm3.2i.mm"

theorem ex-an



  assert |- ( 2 = 2 /\ 3 = 3 )

  proof
    c2
    c2
    wceq
    c3
    c3
    wceq
    c2
    eqid
    c3
    eqid
    pm3.2i
end
