include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "1re.mm"
include "wa.mm"
include "cc0.mm"
include "0lt1.mm"
include "ltaddpos.mm"
include "mpbii.mm"
include "mpan.mm"

theorem ltp1
  let cA: class A


  assert |- ( A e. RR -> A < ( A + 1 ) )

  proof
    c1
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cA
    c1
    caddc
    co
    clt
    wbr
    #
    1re
    @0
    @1
    wa
    cc0
    c1
    clt
    wbr
    @2
    0lt1
    c1
    cA
    ltaddpos
    mpbii
    mpan
end
