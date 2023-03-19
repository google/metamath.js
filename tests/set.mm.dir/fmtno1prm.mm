include "c1.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c5.mm"
include "cprime.mm"
include "fmtno1.mm"
include "5prm.mm"
include "eqeltri.mm"

theorem fmtno1prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 1 ) e. Prime

  proof
    c1
    cfmtno
    cfv
    c5
    cprime
    fmtno1
    5prm
    eqeltri
end
