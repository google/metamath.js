include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "crh.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "pm2mprhm.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "cv1.mm"
include "eqid.mm"
include "pm2mpf1o.mm"
include "wb.mm"
include "pmatring.mm"
include "matring.mm"
include "ply1ring.mm"
include "syl.mm"
include "isrim.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem pm2mprngiso
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T e. ( C RingIso Q ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cT
    cC
    cQ
    crs
    co
    wcel
    #
    cT
    cC
    cQ
    crh
    co
    wcel
    #
    cC
    cbs
    cfv
    #
    cQ
    cbs
    cfv
    #
    cT
    wf1o
    #
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
    pm2mprhm
    cA
    @3
    cC
    cP
    cQ
    cR
    cT
    cQ
    cmgp
    cfv
    cmg
    cfv
    #
    cQ
    cvsca
    cfv
    #
    @4
    cN
    cA
    cv1
    cfv
    #
    pm2mpmhm.p
    pm2mpmhm.c
    @3
    eqid
    #
    @7
    eqid
    @6
    eqid
    @8
    eqid
    pm2mpmhm.a
    pm2mpmhm.q
    @4
    eqid
    #
    pm2mpmhm.t
    pm2mpf1o
    @0
    cC
    crg
    wcel
    cQ
    crg
    wcel
    #
    @1
    @2
    @5
    wa
    wb
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
    @11
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
    @3
    @4
    cC
    cQ
    cT
    crg
    crg
    @9
    @10
    isrim
    syl2anc
    mpbir2and
end
