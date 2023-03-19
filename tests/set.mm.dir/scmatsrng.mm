include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csubrg.mm"
include "cfv.mm"
include "csubg.mm"
include "cur.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "scmatsgrp.mm"
include "scmatid.mm"
include "scmatmulcl.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "wb.mm"
include "matring.mm"
include "eqid.mm"
include "issubrg2.mm"
include "syl.mm"
include "mpbir3and.mm"

theorem scmatsrng
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> S e. ( SubRing ` A ) )

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
    csubrg
    cfv
    wcel
    #
    cS
    cA
    csubg
    cfv
    wcel
    #
    cA
    cur
    cfv
    #
    cS
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
    scmatsgrp
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
    @0
    @8
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
    @5
    @6
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    scmatmulcl
    ralrimivva
    @0
    cA
    crg
    wcel
    @1
    @2
    @4
    @9
    w3a
    wb
    cA
    cR
    cN
    scmatid.a
    matring
    vx
    vy
    cS
    cB
    cA
    @7
    @3
    scmatid.b
    @3
    eqid
    @7
    eqid
    issubrg2
    syl
    mpbir3and
end
