include "ct1.mm"
include "wcel.mm"
include "cnrm.mm"
include "ckq.mm"
include "cfv.mm"
include "creg.mm"
include "t1r0.mm"
include "nrmr0reg.mm"
include "sylan2.mm"

theorem nrmreg
  let cJ: class J


  assert |- ( ( J e. Nrm /\ J e. Fre ) -> J e. Reg )

  proof
    cJ
    ct1
    wcel
    cJ
    cnrm
    wcel
    cJ
    ckq
    cfv
    ct1
    wcel
    cJ
    creg
    wcel
    cJ
    t1r0
    cJ
    nrmr0reg
    sylan2
end
