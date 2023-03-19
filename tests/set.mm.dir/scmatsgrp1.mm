include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "csg.mm"
include "co.mm"
include "wral.mm"
include "scmatdmat.mm"
include "ssrdv.mm"
include "wceq.mm"
include "dmatsgrp.mm"
include "ancoms.mm"
include "subgbas.mm"
include "eqcomd.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "cur.mm"
include "scmatid.mm"
include "ne0i.mm"
include "adantr.mm"
include "wi.mm"
include "com12.mm"
include "impcom.mm"
include "a1d.mm"
include "imp32.mm"
include "w3a.mm"
include "eqid.mm"
include "subgsub.mm"
include "syl3anc.mm"
include "scmatsubcl.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "cgrp.mm"
include "wb.mm"
include "csubrg.mm"
include "dmatsrng.mm"
include "subrgring.mm"
include "ringgrp.mm"
include "issubg4.mm"
include "3syl.mm"
include "mpbir3and.mm"

theorem scmatsgrp1
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> S e. ( SubGrp ` C ) )

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
    csubg
    cfv
    wcel
    #
    cS
    cC
    cbs
    cfv
    #
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
    cC
    csg
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
    @2
    cS
    cD
    @4
    @2
    vx
    cS
    cD
    cA
    cB
    cD
    cR
    cS
    cE
    @7
    cN
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    scmatsgrp1.d
    scmatdmat
    #
    ssrdv
    @2
    cD
    cA
    csubg
    cfv
    wcel
    #
    @4
    cD
    wceq
    @1
    @0
    @14
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
    dmatsgrp
    ancoms
    #
    @14
    cD
    @4
    cD
    cA
    cC
    scmatsgrp1.c
    subgbas
    eqcomd
    syl
    sseqtr4d
    @2
    cA
    cur
    cfv
    #
    cS
    wcel
    @6
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
    @16
    ne0i
    syl
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
    #
    @8
    cS
    wcel
    #
    wa
    #
    wa
    #
    @10
    @7
    @8
    cA
    csg
    cfv
    #
    co
    #
    cS
    @20
    @14
    @7
    cD
    wcel
    #
    @8
    cD
    wcel
    #
    @10
    @22
    wceq
    @2
    @14
    @19
    @15
    adantr
    @19
    @2
    @23
    @17
    @2
    @23
    wi
    @18
    @2
    @17
    @23
    @13
    com12
    adantr
    impcom
    @2
    @17
    @18
    @24
    @2
    @18
    @24
    wi
    @17
    cA
    cB
    cD
    cR
    cS
    cE
    @8
    cN
    c.0
    scmatid.a
    scmatid.b
    scmatid.e
    scmatid.0
    scmatid.s
    scmatsgrp1.d
    scmatdmat
    a1d
    imp32
    @14
    @23
    @24
    w3a
    @22
    @10
    cD
    cA
    cC
    @21
    @9
    @7
    @8
    @21
    eqid
    scmatsgrp1.c
    @9
    eqid
    #
    subgsub
    eqcomd
    syl3anc
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
    scmatsubcl
    eqeltrd
    ralrimivva
    @2
    cC
    crg
    wcel
    #
    cC
    cgrp
    wcel
    @3
    @5
    @6
    @12
    w3a
    wb
    @2
    cD
    cA
    csubrg
    cfv
    wcel
    #
    @26
    @1
    @0
    @27
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
    cD
    cA
    cC
    scmatsgrp1.c
    subrgring
    syl
    cC
    ringgrp
    vx
    vy
    @4
    cS
    cC
    @9
    @4
    eqid
    @25
    issubg4
    3syl
    mpbir3and
end
