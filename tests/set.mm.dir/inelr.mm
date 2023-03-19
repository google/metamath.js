include "ci.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "ine0.mm"
include "neii.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnsymi.mm"
include "ax-mp.mm"
include "caddc.mm"
include "cneg.mm"
include "ixi.mm"
include "renegcli.mm"
include "eqeltri.mm"
include "ltadd1i.mm"
include "ax-1cn.mm"
include "addid2i.mm"
include "ax-i2m1.mm"
include "breq12i.mm"
include "bitri.mm"
include "mtbir.mm"
include "wne.mm"
include "msqgt0.mm"
include "ex.mm"
include "necon1bd.mm"
include "mpi.mm"
include "mto.mm"

theorem inelr



  assert |- -. _i e. RR

  proof
    ci
    cr
    wcel
    #
    ci
    cc0
    wceq
    #
    ci
    cc0
    ine0
    neii
    @0
    cc0
    ci
    ci
    cmul
    co
    #
    clt
    wbr
    #
    wn
    @1
    @3
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    clt
    wbr
    @4
    wn
    0lt1
    cc0
    c1
    0re
    1re
    ltnsymi
    ax-mp
    @3
    cc0
    c1
    caddc
    co
    #
    @2
    c1
    caddc
    co
    #
    clt
    wbr
    @4
    cc0
    @2
    c1
    0re
    @2
    c1
    cneg
    cr
    ixi
    c1
    1re
    renegcli
    eqeltri
    1re
    ltadd1i
    @5
    c1
    @6
    cc0
    clt
    c1
    ax-1cn
    addid2i
    ax-i2m1
    breq12i
    bitri
    mtbir
    @0
    @3
    ci
    cc0
    @0
    ci
    cc0
    wne
    @3
    ci
    msqgt0
    ex
    necon1bd
    mpi
    mto
end
