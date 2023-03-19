include "c3.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c6.mm"
include "3cn.mm"
include "times2i.mm"
include "3p3e6.mm"
include "eqtri.mm"

theorem 3t2e6



  assert |- ( 3 x. 2 ) = 6

  proof
    c3
    c2
    cmul
    co
    c3
    c3
    caddc
    co
    c6
    c3
    3cn
    times2i
    3p3e6
    eqtri
end
