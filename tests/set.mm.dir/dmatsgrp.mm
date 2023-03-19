include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "csg.mm"
include "co.mm"
include "wral.mm"
include "wi.mm"
include "dmatmat.mm"
include "ancoms.mm"
include "ssrdv.mm"
include "cur.mm"
include "dmatid.mm"
include "ne0i.mm"
include "syl.mm"
include "dmatsubcl.mm"
include "ancom1s.mm"
include "ralrimivva.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "matring.mm"
include "ringgrp.mm"
include "eqid.mm"
include "issubg4.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem dmatsgrp
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
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )


  assert |- ( ( R e. Ring /\ N e. Fin ) -> D e. ( SubGrp ` A ) )

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
    csubg
    cfv
    wcel
    #
    cD
    cB
    wss
    #
    cD
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    csg
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
    @2
    vz
    cD
    cB
    @1
    @0
    vz
    cv
    #
    cD
    wcel
    @11
    cB
    wcel
    wi
    cA
    cB
    cD
    cR
    @11
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmat
    ancoms
    ssrdv
    @2
    cA
    cur
    cfv
    #
    cD
    wcel
    #
    @5
    @1
    @0
    @13
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
    cD
    @12
    ne0i
    syl
    @2
    @9
    vx
    vy
    cD
    cD
    @1
    @0
    @6
    cD
    wcel
    @7
    cD
    wcel
    wa
    @9
    cA
    cB
    cD
    cR
    cN
    @6
    @7
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatsubcl
    ancom1s
    ralrimivva
    @2
    cA
    crg
    wcel
    #
    cA
    cgrp
    wcel
    @3
    @4
    @5
    @10
    w3a
    wb
    @1
    @0
    @14
    cA
    cR
    cN
    dmatid.a
    matring
    ancoms
    cA
    ringgrp
    vx
    vy
    cB
    cD
    cA
    @8
    dmatid.b
    @8
    eqid
    issubg4
    3syl
    mpbir3and
end
