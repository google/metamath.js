include "cmnd.mm"
include "csgrp.mm"
include "wss.mm"
include "cv.mm"
include "wnel.mm"
include "wrex.mm"
include "wpss.mm"
include "mndsgrp.mm"
include "ssriv.mm"
include "sgrpnmndex.mm"
include "ssexnelpss.mm"
include "mp2an.mm"

theorem mndsssgrp
  let vx: setvar x


  assert |- Mnd C. SGrp

  proof
    cmnd
    csgrp
    wss
    vx
    cv
    #
    cmnd
    wnel
    vx
    csgrp
    wrex
    cmnd
    csgrp
    wpss
    vx
    cmnd
    csgrp
    @0
    mndsgrp
    ssriv
    vx
    sgrpnmndex
    vx
    cmnd
    csgrp
    ssexnelpss
    mp2an
end
