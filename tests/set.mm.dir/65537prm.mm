include "c4.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c6.mm"
include "c5.mm"
include "cdc.mm"
include "c3.mm"
include "c7.mm"
include "cprime.mm"
include "fmtno4.mm"
include "fmtno4prm.mm"
include "eqeltrri.mm"

theorem 65537prm
  let vk: setvar k
  let vx: setvar x


  assert |- ; ; ; ; 6 5 5 3 7 e. Prime

  proof
    c4
    cfmtno
    cfv
    c6
    c5
    cdc
    c5
    cdc
    c3
    cdc
    c7
    cdc
    cprime
    fmtno4
    fmtno4prm
    eqeltrri
end
