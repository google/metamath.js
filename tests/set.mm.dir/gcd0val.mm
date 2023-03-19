include "cc0.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "wcel.mm"
include "0z.mm"
include "gcdval.mm"
include "mp2an.mm"
include "eqid.mm"
include "iftrue.mm"
include "eqtri.mm"

theorem gcd0val
  let vn: setvar n


  assert |- ( 0 gcd 0 ) = 0

  proof
    cc0
    cc0
    cgcd
    co
    #
    cc0
    cc0
    wceq
    #
    @1
    wa
    #
    cc0
    vn
    cv
    cc0
    cdvds
    wbr
    #
    @3
    wa
    vn
    cz
    crab
    cr
    clt
    csup
    #
    cif
    #
    cc0
    cc0
    cz
    wcel
    #
    @6
    @0
    @5
    wceq
    0z
    0z
    vn
    cc0
    cc0
    gcdval
    mp2an
    @1
    @1
    @5
    cc0
    wceq
    cc0
    eqid
    #
    @7
    @2
    cc0
    @4
    iftrue
    mp2an
    eqtri
end
