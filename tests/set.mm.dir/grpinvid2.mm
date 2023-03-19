include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "oveq1.mm"
include "adantl.mm"
include "grplinv.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "grpinvcl.mm"
include "grplid.mm"
include "syldan.mm"
include "eqcomd.mm"
include "simprr.mm"
include "simprl.mm"
include "adantrr.mm"
include "3jca.mm"
include "grpass.mm"
include "3impb.mm"
include "grprinv.mm"
include "oveq2d.mm"
include "grprid.mm"
include "3adant2.mm"
include "3eqtrd.mm"
include "3eqtr2d.mm"
include "impbida.mm"

theorem grpinvid2
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
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


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( ( N ` X ) = Y <-> ( Y .+ X ) = .0. ) )

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
    cN
    cfv
    #
    cY
    wceq
    #
    cY
    cX
    c.pl
    co
    #
    c.0
    wceq
    #
    @3
    @5
    wa
    @4
    cX
    c.pl
    co
    #
    @6
    c.0
    @5
    @8
    @6
    wceq
    @3
    @4
    cY
    cX
    c.pl
    oveq1
    adantl
    @3
    @8
    c.0
    wceq
    #
    @5
    @0
    @1
    @9
    @2
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
    3adant3
    adantr
    eqtr3d
    @3
    @7
    wa
    @4
    c.0
    @4
    c.pl
    co
    #
    @6
    @4
    c.pl
    co
    #
    cY
    @3
    @4
    @10
    wceq
    @7
    @3
    @10
    @4
    @0
    @1
    @10
    @4
    wceq
    #
    @2
    @0
    @1
    @4
    cB
    wcel
    #
    @12
    cB
    cG
    cN
    cX
    grpinv.b
    grpinv.n
    grpinvcl
    #
    cB
    c.pl
    cG
    @4
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grplid
    syldan
    3adant3
    eqcomd
    adantr
    @7
    @11
    @10
    wceq
    @3
    @6
    c.0
    @4
    c.pl
    oveq1
    adantl
    @3
    @11
    cY
    wceq
    @7
    @3
    @11
    cY
    cX
    @4
    c.pl
    co
    #
    c.pl
    co
    #
    cY
    c.0
    c.pl
    co
    #
    cY
    @0
    @1
    @2
    @11
    @16
    wceq
    #
    @0
    @1
    @2
    wa
    #
    @2
    @1
    @13
    w3a
    @18
    @0
    @19
    wa
    @2
    @1
    @13
    @0
    @1
    @2
    simprr
    @0
    @1
    @2
    simprl
    @0
    @1
    @13
    @2
    @14
    adantrr
    3jca
    cB
    c.pl
    cG
    cY
    cX
    @4
    grpinv.b
    grpinv.p
    grpass
    syldan
    3impb
    @0
    @1
    @16
    @17
    wceq
    @2
    @0
    @1
    wa
    @15
    c.0
    cY
    c.pl
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
    grprinv
    oveq2d
    3adant3
    @0
    @2
    @17
    cY
    wceq
    @1
    cB
    c.pl
    cG
    cY
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grprid
    3adant2
    3eqtrd
    adantr
    3eqtr2d
    impbida
end
