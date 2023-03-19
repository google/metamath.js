include "c4.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c8.mm"
include "4cn.mm"
include "times2i.mm"
include "4p4e8.mm"
include "eqtri.mm"

theorem 4t2e8



  assert |- ( 4 x. 2 ) = 8

  proof
    c4
    c2
    cmul
    co
    c4
    c4
    caddc
    co
    c8
    c4
    4cn
    times2i
    4p4e8
    eqtri
end
