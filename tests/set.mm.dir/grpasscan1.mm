include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "eqid.mm"
include "grprinv.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "wa.mm"
include "wi.mm"
include "grpinvcl.mm"
include "grpass.mm"
include "3exp2.mm"
include "imp.mm"
include "mpd.mm"
include "3impia.mm"
include "grplid.mm"
include "3adant2.mm"
include "3eqtr3d.mm"

theorem grpasscan1
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  assume grplcan.b: |- B = ( Base ` G )
  assume grplcan.p: |- .+ = ( +g ` G )
  assume grpasscan1.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( X .+ ( ( N ` X ) .+ Y ) ) = Y )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cX
    cN
    cfv
    #
    c.pl
    co
    #
    cY
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    cY
    c.pl
    co
    #
    cX
    @4
    cY
    c.pl
    co
    c.pl
    co
    #
    cY
    @3
    @5
    @7
    cY
    c.pl
    @0
    @1
    @5
    @7
    wceq
    @2
    cB
    c.pl
    cG
    cN
    cX
    @7
    grplcan.b
    grplcan.p
    @7
    eqid
    #
    grpasscan1.n
    grprinv
    3adant3
    oveq1d
    @0
    @1
    @2
    @6
    @9
    wceq
    #
    @0
    @1
    wa
    @4
    cB
    wcel
    #
    @2
    @11
    wi
    #
    cB
    cG
    cN
    cX
    grplcan.b
    grpasscan1.n
    grpinvcl
    @0
    @1
    @12
    @13
    wi
    @0
    @1
    @12
    @2
    @11
    cB
    c.pl
    cG
    cX
    @4
    cY
    grplcan.b
    grplcan.p
    grpass
    3exp2
    imp
    mpd
    3impia
    @0
    @2
    @8
    cY
    wceq
    @1
    cB
    c.pl
    cG
    cY
    @7
    grplcan.b
    grplcan.p
    @10
    grplid
    3adant2
    3eqtr3d
end
