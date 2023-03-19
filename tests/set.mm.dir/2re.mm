include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "df-2.mm"
include "1re.mm"
include "readdcli.mm"
include "eqeltri.mm"

theorem 2re



  assert |- 2 e. RR

  proof
    c2
    c1
    c1
    caddc
    co
    cr
    df-2
    c1
    c1
    1re
    1re
    readdcli
    eqeltri
end
