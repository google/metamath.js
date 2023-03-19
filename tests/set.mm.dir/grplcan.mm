include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cminusg.mm"
include "cfv.mm"
include "oveq2.mm"
include "adantl.mm"
include "c0g.mm"
include "eqid.mm"
include "grplinv.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "grpinvcl.mm"
include "adantrl.mm"
include "simprr.mm"
include "simprl.mm"
include "3jca.mm"
include "grpass.mm"
include "syldan.mm"
include "anassrs.mm"
include "grplid.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "adantrr.mm"
include "exp53.mm"
include "3imp2.mm"
include "impbid1.mm"

theorem grplcan
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume grplcan.b: |- B = ( Base ` G )
  assume grplcan.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( Z .+ X ) = ( Z .+ Y ) <-> X = Y ) )

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
    cZ
    cB
    wcel
    #
    w3a
    wa
    cZ
    cX
    c.pl
    co
    #
    cZ
    cY
    c.pl
    co
    #
    wceq
    #
    cX
    cY
    wceq
    #
    @0
    @1
    @2
    @3
    @6
    @7
    wi
    @0
    @1
    @2
    @3
    @6
    @7
    @0
    @1
    wa
    #
    @2
    @3
    wa
    #
    wa
    #
    @6
    wa
    cZ
    cG
    cminusg
    cfv
    #
    cfv
    #
    @4
    c.pl
    co
    #
    @12
    @5
    c.pl
    co
    #
    cX
    cY
    @6
    @13
    @14
    wceq
    @10
    @4
    @5
    @12
    c.pl
    oveq2
    adantl
    @10
    @13
    cX
    wceq
    #
    @6
    @8
    @3
    @15
    @2
    @8
    @3
    wa
    #
    @12
    cZ
    c.pl
    co
    #
    cX
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    cX
    c.pl
    co
    #
    @13
    cX
    @16
    @17
    @19
    cX
    c.pl
    @0
    @3
    @17
    @19
    wceq
    #
    @1
    cB
    c.pl
    cG
    @11
    cZ
    @19
    grplcan.b
    grplcan.p
    @19
    eqid
    #
    @11
    eqid
    #
    grplinv
    #
    adantlr
    oveq1d
    @0
    @1
    @3
    @18
    @13
    wceq
    #
    @0
    @1
    @3
    wa
    #
    @12
    cB
    wcel
    #
    @3
    @1
    w3a
    @25
    @0
    @26
    wa
    @27
    @3
    @1
    @0
    @3
    @27
    @1
    cB
    cG
    @11
    cZ
    grplcan.b
    @23
    grpinvcl
    #
    adantrl
    @0
    @1
    @3
    simprr
    @0
    @1
    @3
    simprl
    3jca
    cB
    c.pl
    cG
    @12
    cZ
    cX
    grplcan.b
    grplcan.p
    grpass
    syldan
    anassrs
    @8
    @20
    cX
    wceq
    @3
    cB
    c.pl
    cG
    cX
    @19
    grplcan.b
    grplcan.p
    @22
    grplid
    adantr
    3eqtr3d
    adantrl
    adantr
    @10
    @14
    cY
    wceq
    #
    @6
    @0
    @9
    @29
    @1
    @0
    @9
    wa
    #
    @17
    cY
    c.pl
    co
    #
    @19
    cY
    c.pl
    co
    #
    @14
    cY
    @30
    @17
    @19
    cY
    c.pl
    @0
    @3
    @21
    @2
    @24
    adantrl
    oveq1d
    @0
    @9
    @27
    @3
    @2
    w3a
    @31
    @14
    wceq
    @30
    @27
    @3
    @2
    @0
    @3
    @27
    @2
    @28
    adantrl
    @0
    @2
    @3
    simprr
    @0
    @2
    @3
    simprl
    3jca
    cB
    c.pl
    cG
    @12
    cZ
    cY
    grplcan.b
    grplcan.p
    grpass
    syldan
    @0
    @2
    @32
    cY
    wceq
    @3
    cB
    c.pl
    cG
    cY
    @19
    grplcan.b
    grplcan.p
    @22
    grplid
    adantrr
    3eqtr3d
    adantlr
    adantr
    3eqtr3d
    exp53
    3imp2
    cX
    cY
    cZ
    c.pl
    oveq2
    impbid1
end
