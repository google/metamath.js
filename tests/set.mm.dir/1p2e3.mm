include "c2.mm"
include "c1.mm"
include "c3.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "2p1e3.mm"
include "addcomli.mm"

theorem 1p2e3



  assert |- ( 1 + 2 ) = 3

  proof
    c2
    c1
    c3
    2cn
    ax-1cn
    2p1e3
    addcomli
end
