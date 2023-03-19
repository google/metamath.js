include "c2.mm"
include "c3.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "2z.mm"
include "iddvds.mm"
include "ax-mp.mm"
include "3m1e2.mm"
include "breqtrri.mm"
include "wb.mm"
include "3z.mm"
include "oddm1even.mm"
include "mpbir.mm"

theorem n2dvds3



  assert |- -. 2 || 3

  proof
    c2
    c3
    cdvds
    wbr
    wn
    #
    c2
    c3
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    c2
    c2
    @1
    cdvds
    c2
    cz
    wcel
    c2
    c2
    cdvds
    wbr
    2z
    c2
    iddvds
    ax-mp
    3m1e2
    breqtrri
    c3
    cz
    wcel
    @0
    @2
    wb
    3z
    c3
    oddm1even
    ax-mp
    mpbir
end
