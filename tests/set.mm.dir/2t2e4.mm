include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c4.mm"
include "2cn.mm"
include "2timesi.mm"
include "2p2e4.mm"
include "eqtri.mm"

theorem 2t2e4



  assert |- ( 2 x. 2 ) = 4

  proof
    c2
    c2
    cmul
    co
    c2
    c2
    caddc
    co
    c4
    c2
    2cn
    2timesi
    2p2e4
    eqtri
end
