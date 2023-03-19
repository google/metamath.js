include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cur.mm"
include "w3a.mm"
include "cmhm.mm"
include "pmatring.mm"
include "eqid.mm"
include "ringmgp.mm"
include "syl.mm"
include "matring.mm"
include "ply1ring.mm"
include "3syl.mm"
include "jca.mm"
include "cmg.mm"
include "cvsca.mm"
include "cv1.mm"
include "mgpbas.mm"
include "eqcomi.mm"
include "pm2mpf.mm"
include "pm2mpmhmlem2.mm"
include "idpm2idmp.mm"
include "3jca.mm"
include "mgpplusg.mm"
include "ringidval.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem pm2mpmhm
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume pm2mpmhm.p: |- P = ( Poly1 ` R )
  assume pm2mpmhm.c: |- C = ( N Mat P )
  assume pm2mpmhm.a: |- A = ( N Mat R )
  assume pm2mpmhm.q: |- Q = ( Poly1 ` A )
  assume pm2mpmhm.t: |- T = ( N pMatToMatPoly R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T e. ( ( mulGrp ` C ) MndHom ( mulGrp ` Q ) ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cC
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    cQ
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    wa
    @1
    cbs
    cfv
    #
    @3
    cbs
    cfv
    #
    cT
    wf
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
    cT
    cfv
    @8
    cT
    cfv
    @9
    cT
    cfv
    cQ
    cmulr
    cfv
    #
    co
    wceq
    vy
    @5
    wral
    vx
    @5
    wral
    #
    cC
    cur
    cfv
    #
    cT
    cfv
    cQ
    cur
    cfv
    #
    wceq
    #
    w3a
    cT
    @1
    @3
    cmhm
    co
    wcel
    @0
    @2
    @4
    @0
    cC
    crg
    wcel
    @2
    cC
    cP
    cR
    cN
    pm2mpmhm.p
    pm2mpmhm.c
    pmatring
    cC
    @1
    @1
    eqid
    #
    ringmgp
    syl
    @0
    cA
    crg
    wcel
    cQ
    crg
    wcel
    @4
    cA
    cR
    cN
    pm2mpmhm.a
    matring
    cQ
    cA
    pm2mpmhm.q
    ply1ring
    cQ
    @3
    @3
    eqid
    #
    ringmgp
    3syl
    jca
    @0
    @7
    @12
    @15
    cA
    @5
    cC
    cP
    cQ
    cR
    cT
    @3
    cmg
    cfv
    #
    cQ
    cvsca
    cfv
    #
    @6
    cN
    cA
    cv1
    cfv
    #
    pm2mpmhm.p
    pm2mpmhm.c
    cC
    cbs
    cfv
    #
    @5
    @21
    cC
    @1
    @16
    @21
    eqid
    #
    mgpbas
    eqcomi
    #
    @19
    eqid
    #
    @18
    eqid
    #
    @20
    eqid
    #
    pm2mpmhm.a
    pm2mpmhm.q
    pm2mpmhm.t
    cQ
    cbs
    cfv
    #
    @6
    @27
    cQ
    @3
    @17
    @27
    eqid
    mgpbas
    eqcomi
    pm2mpf
    vx
    vy
    cA
    @5
    cC
    cP
    cQ
    cR
    cT
    cN
    pm2mpmhm.p
    pm2mpmhm.c
    pm2mpmhm.a
    pm2mpmhm.q
    pm2mpmhm.t
    @23
    pm2mpmhmlem2
    cA
    @21
    cC
    cP
    cQ
    cR
    cT
    @18
    @19
    cN
    @20
    pm2mpmhm.p
    pm2mpmhm.c
    @22
    @24
    @25
    @26
    pm2mpmhm.a
    pm2mpmhm.q
    pm2mpmhm.t
    idpm2idmp
    3jca
    vx
    vy
    @5
    @6
    @10
    @11
    @1
    @3
    cT
    @14
    @13
    @5
    eqid
    @6
    eqid
    cC
    @10
    @1
    @16
    @10
    eqid
    mgpplusg
    cQ
    @11
    @3
    @17
    @11
    eqid
    mgpplusg
    cC
    @13
    @1
    @16
    @13
    eqid
    ringidval
    cQ
    @14
    @3
    @17
    @14
    eqid
    ringidval
    ismhm
    sylanbrc
end
