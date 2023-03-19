include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "cui.mm"
include "cfv.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "cdif.mm"
include "wrex.mm"
include "wo.mm"
include "eqid.mm"
include "ring0cl.mm"
include "anim1i.mm"
include "eldif.mm"
include "sylibr.mm"
include "ringlz.mm"
include "mpdan.mm"
include "adantr.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ex.mm"
include "orrd.mm"
include "wb.mm"
include "isnirred.mm"
include "syl.mm"
include "mpbird.mm"
include "simpr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem irredn0
  let cR: class R
  let cI: class I
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.x: class .x.
  let cU: class U
  let cY: class Y
  let cB: class B
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredn0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ X e. I ) -> X =/= .0. )

  proof
    cR
    crg
    wcel
    #
    cX
    cI
    wcel
    #
    wa
    #
    c.0
    cI
    wcel
    #
    wn
    #
    cX
    c.0
    wne
    @0
    @4
    @1
    @0
    @4
    c.0
    cR
    cui
    cfv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    c.0
    wceq
    #
    vy
    cR
    cbs
    cfv
    #
    @5
    cdif
    #
    wrex
    vx
    @13
    wrex
    #
    wo
    #
    @0
    @6
    @14
    @0
    @6
    wn
    #
    @14
    @0
    @16
    wa
    #
    c.0
    @13
    wcel
    #
    @18
    c.0
    c.0
    @9
    co
    #
    c.0
    wceq
    #
    @14
    @17
    c.0
    @12
    wcel
    #
    @16
    wa
    @18
    @0
    @21
    @16
    @12
    cR
    c.0
    @12
    eqid
    #
    irredn0.z
    ring0cl
    #
    anim1i
    c.0
    @12
    @5
    eldif
    sylibr
    #
    @24
    @0
    @20
    @16
    @0
    @21
    @20
    @23
    @12
    cR
    @9
    c.0
    c.0
    @22
    @9
    eqid
    #
    irredn0.z
    ringlz
    mpdan
    adantr
    @11
    @20
    c.0
    @8
    @9
    co
    #
    c.0
    wceq
    vx
    vy
    c.0
    c.0
    @13
    @13
    @7
    c.0
    wceq
    @10
    @26
    c.0
    @7
    c.0
    @8
    @9
    oveq1
    eqeq1d
    @8
    c.0
    wceq
    @26
    @19
    c.0
    @8
    c.0
    c.0
    @9
    oveq2
    eqeq1d
    rspc2ev
    syl3anc
    ex
    orrd
    @0
    @21
    @4
    @15
    wb
    @23
    vx
    vy
    @12
    cR
    @9
    @5
    cI
    @13
    c.0
    @22
    @5
    eqid
    irredn0.i
    @13
    eqid
    @25
    isnirred
    syl
    mpbird
    adantr
    @2
    @3
    cX
    c.0
    @2
    @1
    cX
    c.0
    wceq
    @3
    @0
    @1
    simpr
    cX
    c.0
    cI
    eleq1
    syl5ibcom
    necon3bd
    mpd
end
