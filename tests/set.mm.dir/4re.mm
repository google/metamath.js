include "c4.mm"
include "c3.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "df-4.mm"
include "3re.mm"
include "1re.mm"
include "readdcli.mm"
include "eqeltri.mm"

theorem 4re



  assert |- 4 e. RR

  proof
    c4
    c3
    c1
    caddc
    co
    cr
    df-4
    c3
    c1
    3re
    1re
    readdcli
    eqeltri
end
