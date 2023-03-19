include "cfn.mm"
include "wcel.mm"
include "crg.mm"
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
include "scmatmat.mm"
include "ssrdv.mm"
include "cur.mm"
include "scmatid.mm"
include "ne0i.mm"
include "syl.mm"
include "scmatsubcl.mm"
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

theorem scmatsgrp
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cN: class N
  let c.0: class .0.
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume scmatid.a: |- A = ( N Mat R )
  assume scmatid.b: |- B = ( Base ` A )
  assume scmatid.e: |- E = ( Base ` R )
  assume scmatid.0: |- .0. = ( 0g ` R )
  assume scmatid.s: |- S = ( N ScMat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> S e. ( SubGrp ` A ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cS
    cA
    csubg
    cfv
    wcel
    #
    cS
    cB
    wss
    #
    cS
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
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @0
    vz
    cS
    cB
    cA
    cB
    cR
    cS
    vz
    cv
    cN
    crg
    scmatid.a
    scmatid.b
    scmatid.s
    scmatmat
    ssrdv
    @0
    cA
    cur
    cfv
    #
    cS
    wcel
    @3
    cA
    cB
    cR
    cS
    cE
    cN
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    scmatid
    cS
    @9
    ne0i
    syl
    @0
    @7
    vx
    vy
    cS
    cS
    cA
    cB
    cR
    cS
    cE
    cN
    @4
    @5
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    scmatsubcl
    ralrimivva
    @0
    cA
    crg
    wcel
    cA
    cgrp
    wcel
    @1
    @2
    @3
    @8
    w3a
    wb
    cA
    cR
    cN
    scmatid.a
    matring
    cA
    ringgrp
    vx
    vy
    cB
    cS
    cA
    @6
    scmatid.b
    @6
    eqid
    issubg4
    3syl
    mpbir3and
end
