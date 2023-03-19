include "cvv.mm"
include "cdm.mm"
include "ssv.mm"
include "cid.mm"
include "dmi.mm"
include "wss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "eqsstr3i.mm"
include "eqssi.mm"

theorem dmv
  let vx: setvar x
  let vy: setvar y


  assert |- dom _V = _V

  proof
    cvv
    cdm
    #
    cvv
    @0
    ssv
    cvv
    cid
    cdm
    #
    @0
    dmi
    cid
    cvv
    wss
    @1
    @0
    wss
    cid
    ssv
    cid
    cvv
    dmss
    ax-mp
    eqsstr3i
    eqssi
end
