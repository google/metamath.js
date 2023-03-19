include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "oveq2.mm"
include "adantl.mm"
include "grprinv.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "grplinv.mm"
include "oveq1d.mm"
include "grpinvcl.mm"
include "adantrr.mm"
include "simprl.mm"
include "simprr.mm"
include "3jca.mm"
include "grpass.mm"
include "syldan.mm"
include "3impb.mm"
include "grplid.mm"
include "3adant2.mm"
include "grprid.mm"
include "3eqtr3rd.mm"
include "impbida.mm"

theorem grpinvid1
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


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( ( N ` X ) = Y <-> ( X .+ Y ) = .0. ) )

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
    cX
    cY
    c.pl
    co
    #
    c.0
    wceq
    #
    @3
    @5
    wa
    cX
    @4
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
    oveq2
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
    grprinv
    3adant3
    adantr
    eqtr3d
    @3
    @7
    wa
    @4
    @6
    c.pl
    co
    #
    @4
    c.0
    c.pl
    co
    #
    cY
    @4
    @7
    @10
    @11
    wceq
    @3
    @6
    c.0
    @4
    c.pl
    oveq2
    adantl
    @3
    @10
    cY
    wceq
    @7
    @3
    c.0
    cY
    c.pl
    co
    #
    @10
    cY
    @3
    @4
    cX
    c.pl
    co
    #
    cY
    c.pl
    co
    #
    @12
    @10
    @0
    @1
    @14
    @12
    wceq
    @2
    @0
    @1
    wa
    @13
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
    grplinv
    oveq1d
    3adant3
    @0
    @1
    @2
    @14
    @10
    wceq
    #
    @0
    @1
    @2
    wa
    #
    @4
    cB
    wcel
    #
    @1
    @2
    w3a
    @15
    @0
    @16
    wa
    @17
    @1
    @2
    @0
    @1
    @17
    @2
    cB
    cG
    cN
    cX
    grpinv.b
    grpinv.n
    grpinvcl
    #
    adantrr
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    3jca
    cB
    c.pl
    cG
    @4
    cX
    cY
    grpinv.b
    grpinv.p
    grpass
    syldan
    3impb
    eqtr3d
    @0
    @2
    @12
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
    grplid
    3adant2
    eqtr3d
    adantr
    @3
    @11
    @4
    wceq
    #
    @7
    @0
    @1
    @19
    @2
    @0
    @1
    @17
    @19
    @18
    cB
    c.pl
    cG
    @4
    c.0
    grpinv.b
    grpinv.p
    grpinv.u
    grprid
    syldan
    3adant3
    adantr
    3eqtr3rd
    impbida
end
