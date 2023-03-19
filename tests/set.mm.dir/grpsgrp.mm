include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "csgrp.mm"
include "grpmnd.mm"
include "mndsgrp.mm"
include "syl.mm"

theorem grpsgrp
  let cG: class G


  assert |- ( G e. Grp -> G e. SGrp )

  proof
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    cG
    csgrp
    wcel
    cG
    grpmnd
    cG
    mndsgrp
    syl
end
