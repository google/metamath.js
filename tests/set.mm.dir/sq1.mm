include "c2.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "2z.mm"
include "1exp.mm"
include "ax-mp.mm"

theorem sq1



  assert |- ( 1 ^ 2 ) = 1

  proof
    c2
    cz
    wcel
    c1
    c2
    cexp
    co
    c1
    wceq
    2z
    c2
    1exp
    ax-mp
end
