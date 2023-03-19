include "c2.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c1.mm"
include "c7.mm"
include "cdc.mm"
include "cprime.mm"
include "fmtno2.mm"
include "17prm.mm"
include "eqeltri.mm"

theorem fmtno2prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 2 ) e. Prime

  proof
    c2
    cfmtno
    cfv
    c1
    c7
    cdc
    cprime
    fmtno2
    17prm
    eqeltri
end
