include "c1q.mm"
include "c1o.mm"
include "cop.mm"
include "cnq.mm"
include "df-1nq.mm"
include "cnpi.mm"
include "wcel.mm"
include "1pi.mm"
include "pinq.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 1nq



  assert |- 1Q e. Q.

  proof
    c1q
    c1o
    c1o
    cop
    #
    cnq
    df-1nq
    c1o
    cnpi
    wcel
    @0
    cnq
    wcel
    1pi
    c1o
    pinq
    ax-mp
    eqeltri
end
