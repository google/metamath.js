include "cnpi.mm"
include "cxp.mm"
include "cnq.mm"
include "cerq.mm"
include "nqerf.mm"
include "ffvelrni.mm"

theorem nqercl
  let cA: class A


  assert |- ( A e. ( N. X. N. ) -> ( /Q ` A ) e. Q. )

  proof
    cnpi
    cnpi
    cxp
    cnq
    cA
    cerq
    nqerf
    ffvelrni
end
