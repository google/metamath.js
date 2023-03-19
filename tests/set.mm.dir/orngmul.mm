include "corng.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "simp2r.mm"
include "simp3r.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "simp2l.mm"
include "simp3l.mm"
include "crg.mm"
include "cogrp.mm"
include "isorng.mm"
include "simp3bi.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "mp2and.mm"

theorem orngmul
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume orngmul.0: |- B = ( Base ` R )
  assume orngmul.1: |- .<_ = ( le ` R )
  assume orngmul.2: |- .0. = ( 0g ` R )
  assume orngmul.3: |- .x. = ( .r ` R )


  assert |- ( ( R e. oRing /\ ( X e. B /\ .0. .<_ X ) /\ ( Y e. B /\ .0. .<_ Y ) ) -> .0. .<_ ( X .x. Y ) )

  proof
    cR
    corng
    wcel
    #
    cX
    cB
    wcel
    #
    c.0
    cX
    c.le
    wbr
    #
    wa
    #
    cY
    cB
    wcel
    #
    c.0
    cY
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @2
    @5
    c.0
    cX
    cY
    c.x
    co
    #
    c.le
    wbr
    #
    @0
    @1
    @2
    @6
    simp2r
    @0
    @3
    @4
    @5
    simp3r
    @7
    @1
    @4
    c.0
    va
    cv
    #
    c.le
    wbr
    #
    c.0
    vb
    cv
    #
    c.le
    wbr
    #
    wa
    #
    c.0
    @10
    @12
    c.x
    co
    #
    c.le
    wbr
    #
    wi
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    @2
    @5
    wa
    #
    @9
    wi
    #
    @0
    @1
    @2
    @6
    simp2l
    @0
    @3
    @4
    @5
    simp3l
    @0
    @3
    @18
    @6
    @0
    cR
    crg
    wcel
    cR
    cogrp
    wcel
    @18
    cB
    cR
    c.x
    c.le
    c.0
    va
    vb
    orngmul.0
    orngmul.2
    orngmul.3
    orngmul.1
    isorng
    simp3bi
    3ad2ant1
    @17
    @20
    @2
    @13
    wa
    #
    c.0
    cX
    @12
    c.x
    co
    #
    c.le
    wbr
    #
    wi
    va
    vb
    cX
    cY
    cB
    cB
    @10
    cX
    wceq
    #
    @14
    @21
    @16
    @23
    @24
    @11
    @2
    @13
    @10
    cX
    c.0
    c.le
    breq2
    anbi1d
    @24
    @15
    @22
    c.0
    c.le
    @10
    cX
    @12
    c.x
    oveq1
    breq2d
    imbi12d
    @12
    cY
    wceq
    #
    @21
    @19
    @23
    @9
    @25
    @13
    @5
    @2
    @12
    cY
    c.0
    c.le
    breq2
    anbi2d
    @25
    @22
    @8
    c.0
    c.le
    @12
    cY
    cX
    c.x
    oveq2
    breq2d
    imbi12d
    rspc2va
    syl21anc
    mp2and
end
