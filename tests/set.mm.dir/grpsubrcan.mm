include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "wb.mm"
include "eqid.mm"
include "grpsubval.mm"
include "3adant2.mm"
include "3adant1.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "grpinvcl.mm"
include "3ad2antr3.mm"
include "grprcan.mm"
include "syl13anc.mm"
include "bitrd.mm"

theorem grpsubrcan
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume grpsubcl.b: |- B = ( Base ` G )
  assume grpsubcl.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .- Z ) = ( Y .- Z ) <-> X = Y ) )

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
    c.mi
    co
    #
    cY
    cZ
    c.mi
    co
    #
    wceq
    #
    cX
    cZ
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cY
    @10
    @11
    co
    #
    wceq
    #
    cX
    cY
    wceq
    #
    @4
    @8
    @14
    wb
    @0
    @4
    @6
    @12
    @7
    @13
    @1
    @3
    @6
    @12
    wceq
    @2
    cB
    @11
    cG
    @9
    c.mi
    cX
    cZ
    grpsubcl.b
    @11
    eqid
    #
    @9
    eqid
    #
    grpsubcl.m
    grpsubval
    3adant2
    @2
    @3
    @7
    @13
    wceq
    @1
    cB
    @11
    cG
    @9
    c.mi
    cY
    cZ
    grpsubcl.b
    @16
    @17
    grpsubcl.m
    grpsubval
    3adant1
    eqeq12d
    adantl
    @5
    @0
    @1
    @2
    @10
    cB
    wcel
    #
    @14
    @15
    wb
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @3
    @18
    @2
    cB
    cG
    @9
    cZ
    grpsubcl.b
    @17
    grpinvcl
    3ad2antr3
    cB
    @11
    cG
    cX
    cY
    @10
    grpsubcl.b
    @16
    grprcan
    syl13anc
    bitrd
end
