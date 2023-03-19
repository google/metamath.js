include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "eqid.mm"
include "grpsubval.mm"
include "3adant1.mm"
include "eqeq1d.mm"
include "wb.mm"
include "simp1.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "simp2.mm"
include "grpinvid2.mm"
include "syl3anc.mm"
include "grpinvinv.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "3bitr2d.mm"

theorem grpsubeq0
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume grpsubid.b: |- B = ( Base ` G )
  assume grpsubid.o: |- .0. = ( 0g ` G )
  assume grpsubid.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( ( X .- Y ) = .0. <-> X = Y ) )

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
    cY
    c.mi
    co
    #
    c.0
    wceq
    cX
    cY
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
    c.0
    wceq
    #
    @6
    @5
    cfv
    #
    cX
    wceq
    #
    cX
    cY
    wceq
    #
    @3
    @4
    @8
    c.0
    @1
    @2
    @4
    @8
    wceq
    @0
    cB
    @7
    cG
    @5
    c.mi
    cX
    cY
    grpsubid.b
    @7
    eqid
    #
    @5
    eqid
    #
    grpsubid.m
    grpsubval
    3adant1
    eqeq1d
    @3
    @0
    @6
    cB
    wcel
    #
    @1
    @11
    @9
    wb
    @0
    @1
    @2
    simp1
    @0
    @2
    @15
    @1
    cB
    cG
    @5
    cY
    grpsubid.b
    @14
    grpinvcl
    3adant2
    @0
    @1
    @2
    simp2
    cB
    @7
    cG
    @5
    @6
    cX
    c.0
    grpsubid.b
    @13
    grpsubid.o
    @14
    grpinvid2
    syl3anc
    @3
    @11
    cY
    cX
    wceq
    @12
    @3
    @10
    cY
    cX
    @0
    @2
    @10
    cY
    wceq
    @1
    cB
    cG
    @5
    cY
    grpsubid.b
    @14
    grpinvinv
    3adant2
    eqeq1d
    cY
    cX
    eqcom
    syl6bb
    3bitr2d
end
