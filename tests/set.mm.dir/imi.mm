include "ci.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "caddc.mm"
include "ax-icn.mm"
include "ax-1cn.mm"
include "mulcli.mm"
include "addid2i.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "mulid1i.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "0re.mm"
include "1re.mm"
include "crim.mm"
include "mp2an.mm"
include "3eqtr3i.mm"

theorem imi



  assert |- ( Im ` _i ) = 1

  proof
    ci
    c1
    cmul
    co
    #
    cim
    cfv
    cc0
    @0
    caddc
    co
    #
    cim
    cfv
    #
    ci
    cim
    cfv
    c1
    @0
    @1
    cim
    @1
    @0
    @0
    ci
    c1
    ax-icn
    ax-1cn
    mulcli
    addid2i
    eqcomi
    fveq2i
    @0
    ci
    cim
    ci
    ax-icn
    mulid1i
    fveq2i
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @2
    c1
    wceq
    0re
    1re
    cc0
    c1
    crim
    mp2an
    3eqtr3i
end
