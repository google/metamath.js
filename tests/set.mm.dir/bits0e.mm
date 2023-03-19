include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "cbits.mm"
include "cfv.mm"
include "wn.mm"
include "2z.mm"
include "dvdsmul1.mm"
include "mpan.mm"
include "wb.mm"
include "a1i.mm"
include "id.mm"
include "zmulcld.mm"
include "bits0.mm"
include "syl.mm"
include "con2bid.mm"
include "mpbid.mm"

theorem bits0e
  let cN: class N


  assert |- ( N e. ZZ -> -. 0 e. ( bits ` ( 2 x. N ) ) )

  proof
    cN
    cz
    wcel
    #
    c2
    c2
    cN
    cmul
    co
    #
    cdvds
    wbr
    #
    cc0
    @1
    cbits
    cfv
    wcel
    #
    wn
    c2
    cz
    wcel
    #
    @0
    @2
    2z
    c2
    cN
    dvdsmul1
    mpan
    @0
    @3
    @2
    @0
    @1
    cz
    wcel
    @3
    @2
    wn
    wb
    @0
    c2
    cN
    @4
    @0
    2z
    a1i
    @0
    id
    zmulcld
    @1
    bits0
    syl
    con2bid
    mpbid
end
