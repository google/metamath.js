include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cco1.mm"
include "cfv.mm"
include "csb.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "matring.mm"
include "adantr.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "cfsupp.mm"
include "wbr.mm"
include "decpmatfsupp.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "gsummoncoe1.mm"
include "wceq.mm"
include "csbov2g.mm"
include "ad2antll.mm"
include "csbvarg.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem pm2mpf1lem
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cN: class N
  let cX: class X
  assume pm2mpf1lem.p: |- P = ( Poly1 ` R )
  assume pm2mpf1lem.c: |- C = ( N Mat P )
  assume pm2mpf1lem.b: |- B = ( Base ` C )
  assume pm2mpf1lem.m: |- .* = ( .s ` Q )
  assume pm2mpf1lem.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpf1lem.x: |- X = ( var1 ` A )
  assume pm2mpf1lem.a: |- A = ( N Mat R )
  assume pm2mpf1lem.q: |- Q = ( Poly1 ` A )

  disjoint A k
  disjoint B k
  disjoint K k
  disjoint N k
  disjoint Q k
  disjoint R k
  disjoint U k
  disjoint .* k
  disjoint .^ k
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( U e. B /\ K e. NN0 ) ) -> ( ( coe1 ` ( Q gsum ( k e. NN0 |-> ( ( U decompPMat k ) .* ( k .^ X ) ) ) ) ) ` K ) = ( U decompPMat K ) )

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
    cU
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
    cQ
    vk
    cn0
    cU
    vk
    cv
    #
    cdecpmat
    co
    #
    @7
    cX
    c.ex
    co
    c.as
    co
    cmpt
    cgsu
    co
    cco1
    cfv
    cfv
    vk
    cK
    @8
    csb
    #
    cU
    vk
    cK
    @7
    csb
    #
    cdecpmat
    co
    #
    cU
    cK
    cdecpmat
    co
    @6
    @8
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
    pm2mpf1lem.q
    @12
    eqid
    pm2mpf1lem.x
    pm2mpf1lem.e
    @2
    cA
    crg
    wcel
    @5
    cA
    cR
    cN
    pm2mpf1lem.a
    matring
    adantr
    @13
    eqid
    #
    pm2mpf1lem.m
    @14
    eqid
    #
    @6
    @8
    @13
    wcel
    #
    vk
    cn0
    @6
    @7
    cn0
    wcel
    #
    wa
    @1
    @3
    @18
    @17
    @0
    @1
    @5
    @18
    simpllr
    @2
    @3
    @4
    @18
    simplrl
    @6
    @18
    simpr
    cA
    cB
    cC
    @13
    cP
    cR
    @7
    cU
    cN
    crg
    pm2mpf1lem.p
    pm2mpf1lem.c
    pm2mpf1lem.b
    pm2mpf1lem.a
    @15
    decpmatcl
    syl3anc
    ralrimiva
    @1
    @3
    vk
    cn0
    @8
    cmpt
    @14
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
    cU
    cN
    @14
    pm2mpf1lem.p
    pm2mpf1lem.c
    pm2mpf1lem.b
    pm2mpf1lem.a
    @16
    decpmatfsupp
    ad2ant2lr
    @2
    @3
    @4
    simprr
    gsummoncoe1
    @4
    @9
    @11
    wceq
    @2
    @3
    vk
    cK
    cU
    @7
    cdecpmat
    cn0
    csbov2g
    ad2antll
    @6
    @10
    cK
    cU
    cdecpmat
    @4
    @10
    cK
    wceq
    @2
    @3
    vk
    cK
    cn0
    csbvarg
    ad2antll
    oveq2d
    3eqtrd
end
