include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "ax-1cn.mm"
include "mul2negi.mm"
include "1t1e1.mm"
include "eqtri.mm"

theorem neg1mulneg1e1



  assert |- ( -u 1 x. -u 1 ) = 1

  proof
    c1
    cneg
    #
    @0
    cmul
    co
    c1
    c1
    cmul
    co
    c1
    c1
    c1
    ax-1cn
    ax-1cn
    mul2negi
    1t1e1
    eqtri
end
