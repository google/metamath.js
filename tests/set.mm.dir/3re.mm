include "c3.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "df-3.mm"
include "2re.mm"
include "1re.mm"
include "readdcli.mm"
include "eqeltri.mm"

theorem 3re



  assert |- 3 e. RR

  proof
    c3
    c2
    c1
    caddc
    co
    cr
    df-3
    c2
    c1
    2re
    1re
    readdcli
    eqeltri
end
