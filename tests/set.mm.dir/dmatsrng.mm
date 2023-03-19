include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "csubrg.mm"
include "cfv.mm"
include "csubg.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "dmatsgrp.mm"
include "dmatid.mm"
include "ancoms.mm"
include "dmatmulcl.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "wb.mm"
include "matring.mm"
include "eqid.mm"
include "issubrg2.mm"
include "syl.mm"
include "mpbir3and.mm"

theorem dmatsrng
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  let vz: setvar z
  let vm: setvar m
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )


  assert |- ( ( R e. Ring /\ N e. Fin ) -> D e. ( SubRing ` A ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cD
    cA
    csubrg
    cfv
    wcel
    #
    cD
    cA
    csubg
    cfv
    wcel
    #
    cA
    cur
    cfv
    #
    cD
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    cmulr
    cfv
    #
    co
    cD
    wcel
    #
    vy
    cD
    wral
    vx
    cD
    wral
    #
    cA
    cB
    cD
    cR
    cN
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatsgrp
    @1
    @0
    @6
    cA
    cB
    cD
    cR
    cN
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatid
    ancoms
    @1
    @0
    @11
    @1
    @0
    wa
    @10
    vx
    vy
    cD
    cD
    cA
    cB
    cD
    cR
    cN
    @7
    @8
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmulcl
    ralrimivva
    ancoms
    @2
    cA
    crg
    wcel
    #
    @3
    @4
    @6
    @11
    w3a
    wb
    @1
    @0
    @12
    cA
    cR
    cN
    dmatid.a
    matring
    ancoms
    vx
    vy
    cD
    cB
    cA
    @9
    @5
    dmatid.b
    @5
    eqid
    @9
    eqid
    issubrg2
    syl
    mpbir3and
end
