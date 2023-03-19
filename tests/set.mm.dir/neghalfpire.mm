include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "halfpire.mm"
include "renegcli.mm"

theorem neghalfpire



  assert |- -u ( _pi / 2 ) e. RR

  proof
    cpi
    c2
    cdiv
    co
    halfpire
    renegcli
end
