include "crngo.mm"
include "ccm2.mm"
include "ccring.mm"
include "df-crngo.mm"
include "elin2.mm"

theorem iscrngo
  let cR: class R


  assert |- ( R e. CRingOps <-> ( R e. RingOps /\ R e. Com2 ) )

  proof
    cR
    crngo
    ccm2
    ccring
    df-crngo
    elin2
end
