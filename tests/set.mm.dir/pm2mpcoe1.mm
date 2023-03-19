include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cn0.mm"
include "cfv.mm"
include "cco1.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csb.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "pm2mpfval.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "matring.mm"
include "adantr.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "ralrimiva.mm"
include "cfsupp.mm"
include "wbr.mm"
include "decpmatfsupp.mm"
include "ad2ant2lr.mm"
include "adantl.mm"
include "gsummoncoe1.mm"
include "csbov2g.mm"
include "csbvarg.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem pm2mpcoe1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vk: setvar k
  let cV: class V
  let va: setvar a
  let vq: setvar q
  assume pm2mpval.p: |- P = ( Poly1 ` R )
  assume pm2mpval.c: |- C = ( N Mat P )
  assume pm2mpval.b: |- B = ( Base ` C )
  assume pm2mpval.m: |- .* = ( .s ` Q )
  assume pm2mpval.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpval.x: |- X = ( var1 ` A )
  assume pm2mpval.a: |- A = ( N Mat R )
  assume pm2mpval.q: |- Q = ( Poly1 ` A )
  assume pm2mpval.t: |- T = ( N pMatToMatPoly R )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( M e. B /\ K e. NN0 ) ) -> ( ( coe1 ` ( T ` M ) ) ` K ) = ( M decompPMat K ) )

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
    cM
    cB
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cK
    cM
    cT
    cfv
    #
    cco1
    cfv
    #
    cfv
    cK
    cQ
    vk
    cn0
    cM
    vk
    cv
    #
    cdecpmat
    co
    #
    @9
    cX
    c.ex
    co
    c.as
    co
    cmpt
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    vk
    cK
    @10
    csb
    #
    cM
    cK
    cdecpmat
    co
    #
    @6
    cK
    @8
    @12
    @6
    @7
    @11
    cco1
    @6
    @0
    @1
    @3
    @7
    @11
    wceq
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    #
    @2
    @3
    @4
    simprl
    #
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    vk
    c.ex
    c.as
    cM
    cN
    crg
    cX
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.m
    pm2mpval.e
    pm2mpval.x
    pm2mpval.a
    pm2mpval.q
    pm2mpval.t
    pm2mpfval
    syl3anc
    fveq2d
    fveq1d
    @6
    @10
    cQ
    cbs
    cfv
    #
    cQ
    cA
    vk
    c.ex
    c.as
    cA
    cbs
    cfv
    #
    cK
    cX
    cA
    c0g
    cfv
    #
    pm2mpval.q
    @17
    eqid
    pm2mpval.x
    pm2mpval.e
    @2
    cA
    crg
    wcel
    @5
    cA
    cR
    cN
    pm2mpval.a
    matring
    adantr
    @18
    eqid
    #
    pm2mpval.m
    @19
    eqid
    #
    @6
    @10
    @18
    wcel
    #
    vk
    cn0
    @6
    @9
    cn0
    wcel
    #
    wa
    @1
    @3
    @23
    @22
    @6
    @1
    @23
    @15
    adantr
    @6
    @3
    @23
    @16
    adantr
    @6
    @23
    simpr
    cA
    cB
    cC
    @18
    cP
    cR
    @9
    cM
    cN
    crg
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.a
    @20
    decpmatcl
    syl3anc
    ralrimiva
    @1
    @3
    vk
    cn0
    @10
    cmpt
    @19
    cfsupp
    wbr
    @0
    @4
    cA
    cB
    cC
    cP
    cR
    vk
    cM
    cN
    @19
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.a
    @21
    decpmatfsupp
    ad2ant2lr
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    gsummoncoe1
    @5
    @13
    @14
    wceq
    #
    @2
    @4
    @24
    @3
    @4
    @13
    cM
    vk
    cK
    @9
    csb
    #
    cdecpmat
    co
    @14
    vk
    cK
    cM
    @9
    cdecpmat
    cn0
    csbov2g
    @4
    @25
    cK
    cM
    cdecpmat
    vk
    cK
    cn0
    csbvarg
    oveq2d
    eqtrd
    adantl
    adantl
    3eqtrd
end
