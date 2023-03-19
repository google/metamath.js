include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "clt.mm"
include "0re.mm"
include "halfre.mm"
include "halfgt0.mm"
include "ltleii.mm"
include "halflt1.mm"
include "1e0p1.mm"
include "breqtri.mm"
include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "wb.mm"
include "0z.mm"
include "flbi.mm"
include "mp2an.mm"
include "mpbir2an.mm"

theorem halffl



  assert |- ( |_ ` ( 1 / 2 ) ) = 0

  proof
    c1
    c2
    cdiv
    co
    #
    cfl
    cfv
    cc0
    wceq
    #
    cc0
    @0
    cle
    wbr
    #
    @0
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    cc0
    @0
    0re
    halfre
    halfgt0
    ltleii
    @0
    c1
    @3
    clt
    halflt1
    1e0p1
    breqtri
    @0
    cr
    wcel
    cc0
    cz
    wcel
    @1
    @2
    @4
    wa
    wb
    halfre
    0z
    @0
    cc0
    flbi
    mp2an
    mpbir2an
end
