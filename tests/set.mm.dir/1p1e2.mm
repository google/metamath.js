include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "df-2.mm"
include "eqcomi.mm"

theorem 1p1e2



  assert |- ( 1 + 1 ) = 2

  proof
    c2
    c1
    c1
    caddc
    co
    df-2
    eqcomi
end
