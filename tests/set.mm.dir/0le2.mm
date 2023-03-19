include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "0le1.mm"
include "1re.mm"
include "addge0i.mm"
include "mp2an.mm"
include "df-2.mm"
include "breqtrri.mm"

theorem 0le2



  assert |- 0 <_ 2

  proof
    cc0
    c1
    c1
    caddc
    co
    #
    c2
    cle
    cc0
    c1
    cle
    wbr
    #
    @1
    cc0
    @0
    cle
    wbr
    0le1
    0le1
    c1
    c1
    1re
    1re
    addge0i
    mp2an
    df-2
    breqtrri
end
