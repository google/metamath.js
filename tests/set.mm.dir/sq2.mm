include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c4.mm"
include "2cn.mm"
include "sqvali.mm"
include "2t2e4.mm"
include "eqtri.mm"

theorem sq2



  assert |- ( 2 ^ 2 ) = 4

  proof
    c2
    c2
    cexp
    co
    c2
    c2
    cmul
    co
    c4
    c2
    2cn
    sqvali
    2t2e4
    eqtri
end
