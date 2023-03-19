include "cogrp.mm"
include "wcel.mm"
include "carchi.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "isarchi3.mm"
include "biimpa.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wceq.mm"
include "breq2.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "breq1.mm"
include "imbi2d.mm"
include "rspc2v.mm"
include "3ad2ant2.mm"
include "mp2d.mm"

theorem archiexdiv
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let vn: setvar n
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume archiexdiv.b: |- B = ( Base ` W )
  assume archiexdiv.0: |- .0. = ( 0g ` W )
  assume archiexdiv.i: |- .< = ( lt ` W )
  assume archiexdiv.x: |- .x. = ( .g ` W )

  disjoint B n
  disjoint W n
  disjoint X n
  disjoint Y n
  disjoint .0. n
  disjoint .< n
  disjoint .x. n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  disjoint Y y
  disjoint .0. x
  disjoint .0. y
  disjoint .< x
  disjoint .< y
  disjoint .x. x
  disjoint .x. y
  assert |- ( ( ( W e. oGrp /\ W e. Archi ) /\ ( X e. B /\ Y e. B ) /\ .0. .< X ) -> E. n e. NN Y .< ( n .x. X ) )

  proof
    cW
    cogrp
    wcel
    #
    cW
    carchi
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    #
    c.0
    cX
    c.lt
    wbr
    #
    w3a
    c.0
    vx
    cv
    #
    c.lt
    wbr
    #
    vy
    cv
    #
    vn
    cv
    #
    @5
    c.x
    co
    #
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @4
    cY
    @8
    cX
    c.x
    co
    #
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    @2
    @3
    @13
    @4
    @0
    @1
    @13
    vx
    vy
    cB
    c.lt
    c.x
    vn
    cW
    c.0
    archiexdiv.b
    archiexdiv.0
    archiexdiv.i
    archiexdiv.x
    isarchi3
    biimpa
    3ad2ant1
    @2
    @3
    @4
    simp3
    @3
    @2
    @13
    @4
    @16
    wi
    #
    wi
    @4
    @12
    @17
    @4
    @7
    @14
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    vx
    vy
    cX
    cY
    cB
    cB
    @5
    cX
    wceq
    #
    @6
    @4
    @11
    @19
    @5
    cX
    c.0
    c.lt
    breq2
    @20
    @10
    @18
    vn
    cn
    @20
    @9
    @14
    @7
    c.lt
    @5
    cX
    @8
    c.x
    oveq2
    breq2d
    rexbidv
    imbi12d
    @7
    cY
    wceq
    #
    @19
    @16
    @4
    @21
    @18
    @15
    vn
    cn
    @7
    cY
    @14
    c.lt
    breq1
    rexbidv
    imbi2d
    rspc2v
    3ad2ant2
    mp2d
end
