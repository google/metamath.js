include "c6.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "cdc.mm"
include "6cn.mm"
include "times2i.mm"
include "6p6e12.mm"
include "eqtri.mm"

theorem 6t2e12



  assert |- ( 6 x. 2 ) = ; 1 2

  proof
    c6
    c2
    cmul
    co
    c6
    c6
    caddc
    co
    c1
    c2
    cdc
    c6
    6cn
    times2i
    6p6e12
    eqtri
end
