include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpidcl.mm"
include "syl.mm"

theorem lmod0vcl
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume 0vcl.v: |- V = ( Base ` W )
  assume 0vcl.z: |- .0. = ( 0g ` W )


  assert |- ( W e. LMod -> .0. e. V )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    c.0
    cV
    wcel
    cW
    lmodgrp
    cV
    cW
    c.0
    0vcl.v
    0vcl.z
    grpidcl
    syl
end
