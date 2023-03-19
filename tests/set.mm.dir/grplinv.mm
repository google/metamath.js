include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crab.mm"
include "crio.mm"
include "grpinvval.mm"
include "adantl.mm"
include "wreu.mm"
include "grpinveu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simprbi.mm"

theorem grplinv
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


  assert |- ( ( G e. Grp /\ X e. B ) -> ( ( N ` X ) .+ X ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cN
    cfv
    #
    vy
    cv
    #
    cX
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    crab
    #
    wcel
    #
    @3
    cX
    c.pl
    co
    #
    c.0
    wceq
    #
    @2
    @3
    @6
    vy
    cB
    crio
    #
    @7
    @1
    @3
    @11
    wceq
    @0
    vy
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
    grpinvval
    adantl
    @2
    @6
    vy
    cB
    wreu
    @11
    @7
    wcel
    vy
    cB
    c.pl
    cG
    cX
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grpinveu
    @6
    vy
    cB
    riotacl2
    syl
    eqeltrd
    @8
    @3
    cB
    wcel
    @10
    @6
    @10
    vy
    @3
    cB
    @4
    @3
    wceq
    @5
    @9
    c.0
    @4
    @3
    cX
    c.pl
    oveq1
    eqeq1d
    elrab
    simprbi
    syl
end
