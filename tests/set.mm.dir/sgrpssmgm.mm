include "csgrp.mm"
include "cmgm.mm"
include "wss.mm"
include "cv.mm"
include "wnel.mm"
include "wrex.mm"
include "wpss.mm"
include "sgrpmgm.mm"
include "ssriv.mm"
include "mgmnsgrpex.mm"
include "ssexnelpss.mm"
include "mp2an.mm"

theorem sgrpssmgm
  let vx: setvar x


  assert |- SGrp C. Mgm

  proof
    csgrp
    cmgm
    wss
    vx
    cv
    #
    csgrp
    wnel
    vx
    cmgm
    wrex
    csgrp
    cmgm
    wpss
    vx
    csgrp
    cmgm
    @0
    sgrpmgm
    ssriv
    vx
    mgmnsgrpex
    vx
    csgrp
    cmgm
    ssexnelpss
    mp2an
end
