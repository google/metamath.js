include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "cgrp.mm"
include "clmlmod.mm"
include "lmodgrp.mm"
include "syl.mm"

theorem clmgrp
  let cW: class W


  assert |- ( W e. CMod -> W e. Grp )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    cW
    clmlmod
    cW
    lmodgrp
    syl
end
