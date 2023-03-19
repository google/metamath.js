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
include "scmatsgrp1.mm"
include "wceq.mm"
include "dmatsrng.mm"
include "ancoms.mm"
include "eqid.mm"
include "subrg1.mm"
include "syl.mm"
include "eqcomd.mm"
include "scmatid.mm"
include "eqeltrd.mm"
include "ressmulr.mm"
include "oveqdr.mm"
include "scmatmulcl.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "wb.mm"
include "subrgring.mm"
include "cbs.mm"
include "issubrg2.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem scmatsrng1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
  assume scmatsgrp1.d: |- D = ( N DMat R )
  assume scmatsgrp1.c: |- C = ( A |`s D )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> S e. ( SubRing ` C ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cS
    cC
    csubrg
    cfv
    wcel
    #
    cS
    cC
    csubg
    cfv
    wcel
    #
    cC
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
    cC
    cmulr
    cfv
    #
    co
    #
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
    cC
    cD
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
    scmatsgrp1.d
    scmatsgrp1.c
    scmatsgrp1
    @2
    @5
    cA
    cur
    cfv
    #
    cS
    @2
    @13
    @5
    @2
    cD
    cA
    csubrg
    cfv
    #
    wcel
    #
    @13
    @5
    wceq
    @1
    @0
    @15
    cA
    cB
    cD
    cR
    cN
    c.0
    scmatid.a
    scmatid.b
    scmatid.0
    scmatsgrp1.d
    dmatsrng
    ancoms
    #
    cD
    cA
    cC
    @13
    scmatsgrp1.c
    @13
    eqid
    subrg1
    syl
    eqcomd
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
    eqeltrd
    @2
    @11
    vx
    vy
    cS
    cS
    @2
    @7
    cS
    wcel
    @8
    cS
    wcel
    wa
    #
    wa
    @10
    @7
    @8
    cA
    cmulr
    cfv
    #
    co
    cS
    @2
    @17
    vx
    vy
    @9
    @18
    @2
    @18
    @9
    @2
    @15
    @18
    @9
    wceq
    @16
    cD
    cA
    cC
    @18
    @14
    scmatsgrp1.c
    @18
    eqid
    ressmulr
    syl
    eqcomd
    oveqdr
    cA
    cB
    cR
    cS
    cE
    cN
    @7
    @8
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    scmatmulcl
    eqeltrd
    ralrimivva
    @2
    @15
    cC
    crg
    wcel
    @3
    @4
    @6
    @12
    w3a
    wb
    @16
    cD
    cA
    cC
    scmatsgrp1.c
    subrgring
    vx
    vy
    cS
    cC
    cbs
    cfv
    #
    cC
    @9
    @5
    @19
    eqid
    @5
    eqid
    @9
    eqid
    issubrg2
    3syl
    mpbir3and
end
