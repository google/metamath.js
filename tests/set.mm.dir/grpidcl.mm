include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "mndidcl.mm"
include "syl.mm"

theorem grpidcl
  let cB: class B
  let cG: class G
  let c.0: class .0.
  assume grpidcl.b: |- B = ( Base ` G )
  assume grpidcl.o: |- .0. = ( 0g ` G )


  assert |- ( G e. Grp -> .0. e. B )

  proof
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    c.0
    cB
    wcel
    cG
    grpmnd
    cB
    cG
    c.0
    grpidcl.b
    grpidcl.o
    mndidcl
    syl
end
