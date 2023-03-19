include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c4.mm"
include "cdvds.mm"
include "cz.mm"
include "wcel.mm"
include "wbr.mm"
include "2z.mm"
include "dvdsmul1.mm"
include "mp2an.mm"
include "2t2e4.mm"
include "breqtri.mm"

theorem z4even



  assert |- 2 || 4

  proof
    c2
    c2
    c2
    cmul
    co
    #
    c4
    cdvds
    c2
    cz
    wcel
    #
    @1
    c2
    @0
    cdvds
    wbr
    2z
    2z
    c2
    c2
    dvdsmul1
    mp2an
    2t2e4
    breqtri
end
