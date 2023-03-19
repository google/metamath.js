include "cmnd.mm"
include "wcel.mm"
include "csgrp.mm"
include "cmgm.mm"
include "mndsgrp.mm"
include "sgrpmgm.mm"
include "syl.mm"

theorem mndmgm
  let cM: class M


  assert |- ( M e. Mnd -> M e. Mgm )

  proof
    cM
    cmnd
    wcel
    cM
    csgrp
    wcel
    cM
    cmgm
    wcel
    cM
    mndsgrp
    cM
    sgrpmgm
    syl
end
