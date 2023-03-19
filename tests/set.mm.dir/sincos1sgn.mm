include "c1.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "ccos.mm"
include "wa.mm"
include "cr.mm"
include "cle.mm"
include "1re.mm"
include "0lt1.mm"
include "1le1.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "elioc2.mm"
include "mp2an.mm"
include "mpbir3an.mm"
include "sin01gt0.mm"
include "cos01gt0.mm"
include "jca.mm"
include "ax-mp.mm"

theorem sincos1sgn



  assert |- ( 0 < ( sin ` 1 ) /\ 0 < ( cos ` 1 ) )

  proof
    c1
    cc0
    c1
    cioc
    co
    wcel
    #
    cc0
    c1
    csin
    cfv
    clt
    wbr
    #
    cc0
    c1
    ccos
    cfv
    clt
    wbr
    #
    wa
    @0
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    c1
    c1
    cle
    wbr
    #
    1re
    0lt1
    1le1
    cc0
    cxr
    wcel
    @3
    @0
    @3
    @4
    @5
    w3a
    wb
    0xr
    1re
    cc0
    c1
    c1
    elioc2
    mp2an
    mpbir3an
    @0
    @1
    @2
    c1
    sin01gt0
    c1
    cos01gt0
    jca
    ax-mp
end
