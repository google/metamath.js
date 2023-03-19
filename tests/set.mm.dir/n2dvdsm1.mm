include "c2.mm"
include "c1.mm"
include "cneg.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "z0even.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "breqtrri.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "neg1z.mm"
include "oddp1even.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem n2dvdsm1



  assert |- -. 2 || -u 1

  proof
    c2
    c1
    cneg
    #
    cdvds
    wbr
    wn
    #
    c2
    @0
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    c2
    cc0
    @2
    cdvds
    z0even
    c1
    @0
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    breqtrri
    @0
    cz
    wcel
    @1
    @3
    wb
    neg1z
    @0
    oddp1even
    ax-mp
    mpbir
end
