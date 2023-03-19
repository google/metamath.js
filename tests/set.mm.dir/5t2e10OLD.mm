include "c5.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c10.mm"
include "5cn.mm"
include "times2i.mm"
include "5p5e10OLD.mm"
include "eqtri.mm"

theorem 5t2e10OLD



  assert |- ( 5 x. 2 ) = 10

  proof
    c5
    c2
    cmul
    co
    c5
    c5
    caddc
    co
    c10
    c5
    5cn
    times2i
    5p5e10OLD
    eqtri
end
