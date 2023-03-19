include "c1.mm"
include "cneg.mm"
include "clog.mm"
include "cfv.mm"
include "ci.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "crp.mm"
include "wcel.mm"
include "wceq.mm"
include "1rp.mm"
include "logneg.mm"
include "ax-mp.mm"
include "log1.mm"
include "oveq1i.mm"
include "ax-icn.mm"
include "picn.mm"
include "mulcli.mm"
include "addid2i.mm"
include "3eqtri.mm"

theorem logm1



  assert |- ( log ` -u 1 ) = ( _i x. _pi )

  proof
    c1
    cneg
    clog
    cfv
    #
    c1
    clog
    cfv
    #
    ci
    cpi
    cmul
    co
    #
    caddc
    co
    #
    cc0
    @2
    caddc
    co
    @2
    c1
    crp
    wcel
    @0
    @3
    wceq
    1rp
    c1
    logneg
    ax-mp
    @1
    cc0
    @2
    caddc
    log1
    oveq1i
    @2
    ci
    cpi
    ax-icn
    picn
    mulcli
    addid2i
    3eqtri
end
