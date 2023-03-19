include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "syl.mm"

theorem ring0cl
  let cB: class B
  let cR: class R
  let c.0: class .0.
  assume ring0cl.b: |- B = ( Base ` R )
  assume ring0cl.z: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> .0. e. B )

  proof
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    c.0
    cB
    wcel
    cR
    ringgrp
    cB
    cR
    c.0
    ring0cl.b
    ring0cl.z
    grpidcl
    syl
end
