include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "c0.mm"
include "wne.mm"
include "lmodgrp.mm"
include "grpbn0.mm"
include "syl.mm"

theorem lmodbn0
  let cB: class B
  let cW: class W
  assume lmodbn0.b: |- B = ( Base ` W )


  assert |- ( W e. LMod -> B =/= (/) )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    cB
    c0
    wne
    cW
    lmodgrp
    cB
    cW
    lmodbn0.b
    grpbn0
    syl
end
