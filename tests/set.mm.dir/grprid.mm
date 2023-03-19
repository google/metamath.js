include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "co.mm"
include "wceq.mm"
include "grpmnd.mm"
include "mndrid.mm"
include "sylan.mm"

theorem grprid
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let c.0: class .0.
  assume grpbn0.b: |- B = ( Base ` G )
  assume grplid.p: |- .+ = ( +g ` G )
  assume grplid.o: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( X .+ .0. ) = X )

  proof
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    cX
    cB
    wcel
    cX
    c.0
    c.pl
    co
    cX
    wceq
    cG
    grpmnd
    cB
    c.pl
    cG
    cX
    c.0
    grpbn0.b
    grplid.p
    grplid.o
    mndrid
    sylan
end
