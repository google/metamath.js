include "cc0.mm"
include "ci.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cre.mm"
include "cfv.mm"
include "ax-icn.mm"
include "ax-1cn.mm"
include "mulcli.mm"
include "addid2i.mm"
include "fveq2i.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "0re.mm"
include "1re.mm"
include "crre.mm"
include "mp2an.mm"
include "mulid1i.mm"
include "3eqtr3ri.mm"

theorem rei



  assert |- ( Re ` _i ) = 0

  proof
    cc0
    ci
    c1
    cmul
    co
    #
    caddc
    co
    #
    cre
    cfv
    #
    @0
    cre
    cfv
    cc0
    ci
    cre
    cfv
    @1
    @0
    cre
    @0
    ci
    c1
    ax-icn
    ax-1cn
    mulcli
    addid2i
    fveq2i
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @2
    cc0
    wceq
    0re
    1re
    cc0
    c1
    crre
    mp2an
    @0
    ci
    cre
    ci
    ax-icn
    mulid1i
    fveq2i
    3eqtr3ri
end
