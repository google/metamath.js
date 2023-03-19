include "c1.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "negne0i.mm"

theorem neg1ne0



  assert |- -u 1 =/= 0

  proof
    c1
    ax-1cn
    ax-1ne0
    negne0i
end
