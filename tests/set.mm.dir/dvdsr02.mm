include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "ring0cl.mm"
include "adantr.mm"
include "eqid.mm"
include "dvdsr2.mm"
include "syl.mm"
include "ringrz.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "cgrp.mm"
include "c0.mm"
include "wne.mm"
include "ringgrp.mm"
include "grpbn0.mm"
include "r19.9rzv.mm"
include "3syl.mm"
include "bitr4d.mm"
include "bitrd.mm"

theorem dvdsr02
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume dvdsr0.b: |- B = ( Base ` R )
  assume dvdsr0.d: |- .|| = ( ||r ` R )
  assume dvdsr0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ X e. B ) -> ( .0. .|| X <-> X = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c.0
    cX
    c.pa
    wbr
    #
    vx
    cv
    #
    c.0
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    wceq
    #
    vx
    cB
    wrex
    #
    cX
    c.0
    wceq
    #
    @2
    c.0
    cB
    wcel
    #
    @3
    @8
    wb
    @0
    @10
    @1
    cB
    cR
    c.0
    dvdsr0.b
    dvdsr0.z
    ring0cl
    adantr
    vx
    cB
    c.pa
    cR
    @5
    c.0
    cX
    dvdsr0.b
    dvdsr0.d
    @5
    eqid
    #
    dvdsr2
    syl
    @0
    @8
    @9
    wb
    @1
    @0
    @8
    @9
    vx
    cB
    wrex
    #
    @9
    @0
    @7
    @9
    vx
    cB
    @0
    @4
    cB
    wcel
    wa
    #
    @7
    c.0
    cX
    wceq
    @9
    @13
    @6
    c.0
    cX
    cB
    cR
    @5
    @4
    c.0
    dvdsr0.b
    @11
    dvdsr0.z
    ringrz
    eqeq1d
    c.0
    cX
    eqcom
    syl6bb
    rexbidva
    @0
    cR
    cgrp
    wcel
    cB
    c0
    wne
    @9
    @12
    wb
    cR
    ringgrp
    cB
    cR
    dvdsr0.b
    grpbn0
    @9
    vx
    cB
    r19.9rzv
    3syl
    bitr4d
    adantr
    bitrd
end
