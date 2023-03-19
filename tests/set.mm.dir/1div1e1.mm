include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "div1.mm"
include "ax-mp.mm"

theorem 1div1e1



  assert |- ( 1 / 1 ) = 1

  proof
    c1
    cc
    wcel
    c1
    c1
    cdiv
    co
    c1
    wceq
    ax-1cn
    c1
    div1
    ax-mp
end
