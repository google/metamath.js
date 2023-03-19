include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "ctop.mm"
include "elfvdm.mm"
include "wfn.mm"
include "wceq.mm"
include "fncld.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleq.mm"

theorem cldrcl
  let cC: class C
  let cJ: class J


  assert |- ( C e. ( Clsd ` J ) -> J e. Top )

  proof
    cC
    cJ
    ccld
    cfv
    wcel
    cJ
    ccld
    cdm
    #
    ctop
    cC
    cJ
    ccld
    elfvdm
    ccld
    ctop
    wfn
    @0
    ctop
    wceq
    fncld
    ctop
    ccld
    fndm
    ax-mp
    syl6eleq
end
