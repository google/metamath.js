include "c0.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cc0.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "0mbl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ovol0.mm"
include "eqtri.mm"

theorem vol0
  let vk: setvar k
  let vx: setvar x


  assert |- ( vol ` (/) ) = 0

  proof
    c0
    cvol
    cfv
    #
    c0
    covol
    cfv
    #
    cc0
    c0
    cvol
    cdm
    wcel
    @0
    @1
    wceq
    0mbl
    c0
    mblvol
    ax-mp
    ovol0
    eqtri
end
