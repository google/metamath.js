include "cpi.mm"
include "picn.mm"
include "negcli.mm"

theorem negpicn



  assert |- -u _pi e. CC

  proof
    cpi
    picn
    negcli
end
