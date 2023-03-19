include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "wb.mm"
include "0re.mm"
include "1re.mm"
include "ltsub2.mm"
include "mp3an12.mm"
include "mpbii.mm"
include "recn.mm"
include "subid1d.mm"
include "breqtrd.mm"

theorem ltm1
  let cA: class A


  assert |- ( A e. RR -> ( A - 1 ) < A )

  proof
    cA
    cr
    wcel
    #
    cA
    c1
    cmin
    co
    #
    cA
    cc0
    cmin
    co
    #
    cA
    clt
    @0
    cc0
    c1
    clt
    wbr
    #
    @1
    @2
    clt
    wbr
    #
    0lt1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @0
    @3
    @4
    wb
    0re
    1re
    cc0
    c1
    cA
    ltsub2
    mp3an12
    mpbii
    @0
    cA
    cA
    recn
    subid1d
    breqtrd
end
