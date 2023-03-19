include "c8.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "8cn.mm"
include "times2i.mm"
include "8p8e16.mm"
include "eqtri.mm"

theorem 8t2e16



  assert |- ( 8 x. 2 ) = ; 1 6

  proof
    c8
    c2
    cmul
    co
    c8
    c8
    caddc
    co
    c1
    c6
    cdc
    c8
    8cn
    times2i
    8p8e16
    eqtri
end
