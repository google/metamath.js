include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "1z.mm"
include "mulgdir.mm"
include "mp3anr2.mm"
include "3impb.mm"
include "mulg1.mm"
include "3ad2ant3.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem mulgp1
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume mulgnndir.b: |- B = ( Base ` G )
  assume mulgnndir.t: |- .x. = ( .g ` G )
  assume mulgnndir.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( ( N + 1 ) .x. X ) = ( ( N .x. X ) .+ X ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cN
    c1
    caddc
    co
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    c1
    cX
    c.x
    co
    #
    c.pl
    co
    #
    @5
    cX
    c.pl
    co
    @0
    @1
    @2
    @4
    @7
    wceq
    #
    @0
    @1
    c1
    cz
    wcel
    @2
    @8
    1z
    cB
    c.pl
    c.x
    cG
    cN
    c1
    cX
    mulgnndir.b
    mulgnndir.t
    mulgnndir.p
    mulgdir
    mp3anr2
    3impb
    @3
    @6
    cX
    @5
    c.pl
    @2
    @0
    @6
    cX
    wceq
    @1
    cB
    c.x
    cG
    cX
    mulgnndir.b
    mulgnndir.t
    mulg1
    3ad2ant3
    oveq2d
    eqtrd
end
