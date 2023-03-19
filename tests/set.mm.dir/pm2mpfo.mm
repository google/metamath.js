include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "pm2mpf.mm"
include "cn0.mm"
include "cco1.mm"
include "co.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "eqid.mm"
include "mp2pm2mp.mm"
include "3expa.mm"
include "wi.mm"
include "mply1topmatcl.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcedv.mm"
include "com12.mm"
include "eqcoms.mm"
include "mpcom.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem pm2mpfo
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let c.ex: class .^
  let c.as: class .*
  let cL: class L
  let cN: class N
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vf: setvar f
  let vp: setvar p
  let vl: setvar l
  assume pm2mpfo.p: |- P = ( Poly1 ` R )
  assume pm2mpfo.c: |- C = ( N Mat P )
  assume pm2mpfo.b: |- B = ( Base ` C )
  assume pm2mpfo.m: |- .* = ( .s ` Q )
  assume pm2mpfo.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpfo.x: |- X = ( var1 ` A )
  assume pm2mpfo.a: |- A = ( N Mat R )
  assume pm2mpfo.q: |- Q = ( Poly1 ` A )
  assume pm2mpfo.l: |- L = ( Base ` Q )
  assume pm2mpfo.t: |- T = ( N pMatToMatPoly R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : B -onto-> L )

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
    cB
    cL
    cT
    wf
    vp
    cv
    #
    vf
    cv
    #
    cT
    cfv
    #
    wceq
    #
    vf
    cB
    wrex
    #
    vp
    cL
    wral
    cB
    cL
    cT
    wfo
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    c.ex
    c.as
    cL
    cN
    cX
    pm2mpfo.p
    pm2mpfo.c
    pm2mpfo.b
    pm2mpfo.m
    pm2mpfo.e
    pm2mpfo.x
    pm2mpfo.a
    pm2mpfo.q
    pm2mpfo.t
    pm2mpfo.l
    pm2mpf
    @2
    @7
    vp
    cL
    @3
    vl
    cL
    vi
    vj
    cN
    cN
    cP
    vk
    cn0
    vi
    cv
    vj
    cv
    vk
    cv
    #
    vl
    cv
    cco1
    cfv
    cfv
    co
    @8
    cR
    cv1
    cfv
    #
    cP
    cmgp
    cfv
    cmg
    cfv
    #
    co
    cP
    cvsca
    cfv
    #
    co
    cmpt
    cgsu
    co
    cmpt2
    cmpt
    #
    cfv
    #
    cT
    cfv
    #
    @3
    wceq
    #
    @2
    @3
    cL
    wcel
    #
    wa
    #
    @7
    @0
    @1
    @16
    @15
    cA
    cP
    cQ
    cR
    cT
    @11
    vi
    vj
    vk
    @10
    @12
    cL
    cN
    @3
    @9
    vl
    pm2mpfo.a
    pm2mpfo.q
    pm2mpfo.l
    @11
    eqid
    #
    @10
    eqid
    #
    @9
    eqid
    #
    @12
    eqid
    #
    pm2mpfo.p
    pm2mpfo.t
    mp2pm2mp
    3expa
    @17
    @7
    wi
    @3
    @14
    @17
    @3
    @14
    wceq
    #
    @7
    @17
    @6
    @22
    vf
    @13
    cB
    @0
    @1
    @16
    @13
    cB
    wcel
    cA
    cB
    cC
    cP
    cQ
    cR
    @11
    vi
    vj
    vk
    @10
    @12
    cL
    cN
    @3
    @9
    vl
    pm2mpfo.a
    pm2mpfo.q
    pm2mpfo.l
    pm2mpfo.p
    @18
    @19
    @20
    @21
    pm2mpfo.c
    pm2mpfo.b
    mply1topmatcl
    3expa
    @17
    @4
    @13
    wceq
    #
    wa
    #
    @5
    @14
    @3
    @24
    @4
    @13
    cT
    @17
    @23
    simpr
    fveq2d
    eqeq2d
    rspcedv
    com12
    eqcoms
    mpcom
    ralrimiva
    vf
    vp
    cB
    cL
    cT
    dffo3
    sylanbrc
end
