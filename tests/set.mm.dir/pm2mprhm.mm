include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "pmatring.mm"
include "matring.mm"
include "ply1ring.mm"
include "syl.mm"
include "jca.mm"
include "cbs.mm"
include "cmg.mm"
include "cvsca.mm"
include "cv1.mm"
include "eqid.mm"
include "pm2mpghm.mm"
include "pm2mpmhm.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem pm2mprhm
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T e. ( C RingHom Q ) )

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
    crg
    wcel
    #
    cQ
    crg
    wcel
    #
    wa
    cT
    cC
    cQ
    cghm
    co
    wcel
    #
    cT
    cC
    cmgp
    cfv
    #
    cQ
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    cT
    cC
    cQ
    crh
    co
    wcel
    @0
    @1
    @2
    cC
    cP
    cR
    cN
    pm2mpmhm.p
    pm2mpmhm.c
    pmatring
    @0
    cA
    crg
    wcel
    @2
    cA
    cR
    cN
    pm2mpmhm.a
    matring
    cQ
    cA
    pm2mpmhm.q
    ply1ring
    syl
    jca
    @0
    @3
    @6
    cA
    cC
    cbs
    cfv
    #
    cC
    cP
    cQ
    cR
    cT
    @5
    cmg
    cfv
    #
    cQ
    cvsca
    cfv
    #
    cQ
    cbs
    cfv
    #
    cN
    cA
    cv1
    cfv
    #
    pm2mpmhm.p
    pm2mpmhm.c
    @7
    eqid
    @9
    eqid
    @8
    eqid
    @11
    eqid
    pm2mpmhm.a
    pm2mpmhm.q
    @10
    eqid
    pm2mpmhm.t
    pm2mpghm
    cA
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
    pm2mpmhm
    jca
    cC
    cQ
    cT
    @4
    @5
    @4
    eqid
    @5
    eqid
    isrhm
    sylanbrc
end
