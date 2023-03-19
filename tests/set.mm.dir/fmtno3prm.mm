include "c3.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c2.mm"
include "c5.mm"
include "cdc.mm"
include "c7.mm"
include "cprime.mm"
include "fmtno3.mm"
include "257prm.mm"
include "eqeltri.mm"

theorem fmtno3prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 3 ) e. Prime

  proof
    c3
    cfmtno
    cfv
    c2
    c5
    cdc
    c7
    cdc
    cprime
    fmtno3
    257prm
    eqeltri
end
