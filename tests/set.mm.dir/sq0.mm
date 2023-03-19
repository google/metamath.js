include "cc0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "0cn.mm"
include "sqeq0i.mm"
include "mpbir.mm"

theorem sq0



  assert |- ( 0 ^ 2 ) = 0

  proof
    cc0
    c2
    cexp
    co
    cc0
    wceq
    cc0
    cc0
    wceq
    cc0
    eqid
    cc0
    0cn
    sqeq0i
    mpbir
end
