include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "grpcl.mm"
include "grpidcl.mm"
include "grplid.mm"
include "grpass.mm"
include "grpinvex.mm"
include "simpr.mm"
include "grpinvcl.mm"
include "grplinv.mm"
include "grprinvd.mm"

theorem grprinv
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let ve: setvar e
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume grpinv.b: |- B = ( Base ` G )
  assume grpinv.p: |- .+ = ( +g ` G )
  assume grpinv.u: |- .0. = ( 0g ` G )
  assume grpinv.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( X .+ ( N ` X ) ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    vx
    vy
    vz
    cB
    c.pl
    cX
    cN
    cfv
    c.0
    cX
    cB
    c.pl
    cG
    vx
    cv
    #
    vy
    cv
    #
    grpinv.b
    grpinv.p
    grpcl
    cB
    cG
    c.0
    grpinv.b
    grpinv.u
    grpidcl
    cB
    c.pl
    cG
    @2
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grplid
    cB
    c.pl
    cG
    @2
    @3
    vz
    cv
    grpinv.b
    grpinv.p
    grpass
    vy
    cB
    c.pl
    cG
    @2
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grpinvex
    @0
    @1
    simpr
    cB
    cG
    cN
    cX
    grpinv.b
    grpinv.n
    grpinvcl
    cB
    c.pl
    cG
    cN
    cX
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grpinv.n
    grplinv
    grprinvd
end
