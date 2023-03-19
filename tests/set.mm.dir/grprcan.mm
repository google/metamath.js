include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "wi.mm"
include "wrex.mm"
include "eqid.mm"
include "grpinvex.mm"
include "3ad2antr3.mm"
include "simprr.mm"
include "oveq1d.mm"
include "simpll.mm"
include "grpass.mm"
include "sylan.mm"
include "simplr1.mm"
include "simplr3.mm"
include "simprll.mm"
include "caovassd.mm"
include "simplr2.mm"
include "3eqtr3d.mm"
include "grpcl.mm"
include "syl3an1.mm"
include "grpidcl.mm"
include "syl.mm"
include "grplid.mm"
include "simpr.mm"
include "adantr.mm"
include "simprlr.mm"
include "grprinvd.mm"
include "mpdan.mm"
include "oveq2d.mm"
include "grprid.mm"
include "syl2anc.mm"
include "expr.mm"
include "rexlimddv.mm"
include "oveq1.mm"
include "impbid1.mm"

theorem grprcan
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume grprcan.b: |- B = ( Base ` G )
  assume grprcan.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Z ) = ( Y .+ Z ) <-> X = Y ) )

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
    #
    wa
    #
    cX
    cZ
    c.pl
    co
    #
    cY
    cZ
    c.pl
    co
    #
    wceq
    #
    cX
    cY
    wceq
    #
    @5
    vy
    cv
    #
    cZ
    c.pl
    co
    cG
    c0g
    cfv
    #
    wceq
    #
    @8
    @9
    wi
    vy
    cB
    @0
    @1
    @3
    @12
    vy
    cB
    wrex
    @2
    vy
    cB
    c.pl
    cG
    cZ
    @11
    grprcan.b
    grprcan.p
    @11
    eqid
    #
    grpinvex
    3ad2antr3
    @5
    @10
    cB
    wcel
    #
    @12
    wa
    #
    @8
    @9
    @5
    @15
    @8
    wa
    #
    wa
    #
    cX
    @11
    c.pl
    co
    #
    cY
    @11
    c.pl
    co
    #
    cX
    cY
    @17
    cX
    cZ
    @10
    c.pl
    co
    #
    c.pl
    co
    #
    cY
    @20
    c.pl
    co
    #
    @18
    @19
    @17
    @6
    @10
    c.pl
    co
    @7
    @10
    c.pl
    co
    @21
    @22
    @17
    @6
    @7
    @10
    c.pl
    @5
    @15
    @8
    simprr
    oveq1d
    @17
    vu
    vv
    vw
    cX
    cZ
    @10
    cB
    c.pl
    @17
    @0
    vu
    cv
    #
    cB
    wcel
    #
    vv
    cv
    #
    cB
    wcel
    #
    vw
    cv
    #
    cB
    wcel
    w3a
    @23
    @25
    c.pl
    co
    #
    @27
    c.pl
    co
    @23
    @25
    @27
    c.pl
    co
    c.pl
    co
    wceq
    @0
    @4
    @16
    simpll
    #
    cB
    c.pl
    cG
    @23
    @25
    @27
    grprcan.b
    grprcan.p
    grpass
    sylan
    #
    @1
    @2
    @3
    @0
    @16
    simplr1
    #
    @1
    @2
    @3
    @0
    @16
    simplr3
    #
    @5
    @14
    @12
    @8
    simprll
    #
    caovassd
    @17
    vu
    vv
    vw
    cY
    cZ
    @10
    cB
    c.pl
    @30
    @1
    @2
    @3
    @0
    @16
    simplr2
    #
    @32
    @33
    caovassd
    3eqtr3d
    @17
    @20
    @11
    cX
    c.pl
    @17
    @3
    @20
    @11
    wceq
    @32
    @17
    @3
    vu
    vv
    vw
    cB
    c.pl
    @10
    @11
    cZ
    @17
    @0
    @24
    @26
    @28
    cB
    wcel
    @29
    cB
    c.pl
    cG
    @23
    @25
    grprcan.b
    grprcan.p
    grpcl
    syl3an1
    @17
    @0
    @11
    cB
    wcel
    @29
    cB
    cG
    @11
    grprcan.b
    @13
    grpidcl
    syl
    @17
    @0
    @24
    @11
    @23
    c.pl
    co
    @23
    wceq
    @29
    cB
    c.pl
    cG
    @23
    @11
    grprcan.b
    grprcan.p
    @13
    grplid
    sylan
    @30
    @17
    @0
    @24
    @25
    @23
    c.pl
    co
    @11
    wceq
    vv
    cB
    wrex
    @29
    vv
    cB
    c.pl
    cG
    @23
    @11
    grprcan.b
    grprcan.p
    @13
    grpinvex
    sylan
    @17
    @3
    simpr
    @17
    @14
    @3
    @33
    adantr
    @17
    @12
    @3
    @5
    @14
    @12
    @8
    simprlr
    adantr
    grprinvd
    mpdan
    #
    oveq2d
    @17
    @20
    @11
    cY
    c.pl
    @35
    oveq2d
    3eqtr3d
    @17
    @0
    @1
    @18
    cX
    wceq
    @29
    @31
    cB
    c.pl
    cG
    cX
    @11
    grprcan.b
    grprcan.p
    @13
    grprid
    syl2anc
    @17
    @0
    @2
    @19
    cY
    wceq
    @29
    @34
    cB
    c.pl
    cG
    cY
    @11
    grprcan.b
    grprcan.p
    @13
    grprid
    syl2anc
    3eqtr3d
    expr
    rexlimddv
    cX
    cY
    cZ
    c.pl
    oveq1
    impbid1
end
