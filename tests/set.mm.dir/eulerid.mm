include "ci.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cneg.mm"
include "cc0.mm"
include "efipi.mm"
include "oveq1i.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "eqtri.mm"

theorem eulerid



  assert |- ( ( exp ` ( _i x. _pi ) ) + 1 ) = 0

  proof
    ci
    cpi
    cmul
    co
    ce
    cfv
    #
    c1
    caddc
    co
    c1
    cneg
    #
    c1
    caddc
    co
    cc0
    @0
    @1
    c1
    caddc
    efipi
    oveq1i
    c1
    @1
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    eqtri
end
