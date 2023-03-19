include "cc0.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c3.mm"
include "cprime.mm"
include "fmtno0.mm"
include "3prm.mm"
include "eqeltri.mm"

theorem fmtno0prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 0 ) e. Prime

  proof
    cc0
    cfmtno
    cfv
    c3
    cprime
    fmtno0
    3prm
    eqeltri
end
