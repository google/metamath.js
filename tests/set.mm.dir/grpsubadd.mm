include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cminusg.mm"
include "cfv.mm"
include "eqid.mm"
include "grpsubval.mm"
include "3adant3.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "wb.mm"
include "simpl.mm"
include "simpr1.mm"
include "grpinvcl.mm"
include "3ad2antr2.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "simpr2.mm"
include "grprcan.mm"
include "syl13anc.mm"
include "c0g.mm"
include "grpass.mm"
include "grplinv.mm"
include "oveq2d.mm"
include "grprid.mm"
include "3ad2antr1.mm"
include "3eqtrd.mm"
include "3bitr2d.mm"
include "eqcom.mm"
include "syl6bb.mm"

theorem grpsubadd
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume grpsubadd.b: |- B = ( Base ` G )
  assume grpsubadd.p: |- .+ = ( +g ` G )
  assume grpsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .- Y ) = Z <-> ( Z .+ Y ) = X ) )

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
    cY
    c.mi
    co
    #
    cZ
    wceq
    #
    cX
    cZ
    cY
    c.pl
    co
    #
    wceq
    #
    @8
    cX
    wceq
    @5
    @7
    cX
    cY
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    cZ
    wceq
    #
    @12
    cY
    c.pl
    co
    #
    @8
    wceq
    #
    @9
    @5
    @6
    @12
    cZ
    @4
    @6
    @12
    wceq
    #
    @0
    @1
    @2
    @16
    @3
    cB
    c.pl
    cG
    @10
    c.mi
    cX
    cY
    grpsubadd.b
    grpsubadd.p
    @10
    eqid
    #
    grpsubadd.m
    grpsubval
    3adant3
    adantl
    eqeq1d
    @5
    @0
    @12
    cB
    wcel
    #
    @3
    @2
    @15
    @13
    wb
    @0
    @4
    simpl
    #
    @5
    @0
    @1
    @11
    cB
    wcel
    #
    @18
    @19
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @20
    @3
    cB
    cG
    @10
    cY
    grpsubadd.b
    @17
    grpinvcl
    3ad2antr2
    #
    cB
    c.pl
    cG
    cX
    @11
    grpsubadd.b
    grpsubadd.p
    grpcl
    syl3anc
    @0
    @1
    @2
    @3
    simpr3
    @0
    @1
    @2
    @3
    simpr2
    #
    cB
    c.pl
    cG
    @12
    cZ
    cY
    grpsubadd.b
    grpsubadd.p
    grprcan
    syl13anc
    @5
    @14
    cX
    @8
    @5
    @14
    cX
    @11
    cY
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    cG
    c0g
    cfv
    #
    c.pl
    co
    #
    cX
    @5
    @0
    @1
    @20
    @2
    @14
    @25
    wceq
    @19
    @21
    @22
    @23
    cB
    c.pl
    cG
    cX
    @11
    cY
    grpsubadd.b
    grpsubadd.p
    grpass
    syl13anc
    @5
    @24
    @26
    cX
    c.pl
    @0
    @1
    @2
    @24
    @26
    wceq
    @3
    cB
    c.pl
    cG
    @10
    cY
    @26
    grpsubadd.b
    grpsubadd.p
    @26
    eqid
    #
    @17
    grplinv
    3ad2antr2
    oveq2d
    @0
    @2
    @1
    @27
    cX
    wceq
    @3
    cB
    c.pl
    cG
    cX
    @26
    grpsubadd.b
    grpsubadd.p
    @28
    grprid
    3ad2antr1
    3eqtrd
    eqeq1d
    3bitr2d
    cX
    @8
    eqcom
    syl6bb
end
