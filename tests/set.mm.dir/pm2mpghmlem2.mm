include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cvv.mm"
include "c0g.mm"
include "nn0ex.mm"
include "a1i.mm"
include "clmod.mm"
include "matring.mm"
include "3adant3.mm"
include "ply1lmod.mm"
include "syl.mm"
include "csca.mm"
include "wceq.mm"
include "ply1sca.mm"
include "eqid.mm"
include "wa.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "cmpt.mm"
include "cfsupp.mm"
include "wbr.mm"
include "decpmatfsupp.mm"
include "3adant1.mm"
include "mptscmfsupp0.mm"

theorem pm2mpghmlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cX: class X
  assume pm2mpfo.p: |- P = ( Poly1 ` R )
  assume pm2mpfo.c: |- C = ( N Mat P )
  assume pm2mpfo.b: |- B = ( Base ` C )
  assume pm2mpfo.m: |- .* = ( .s ` Q )
  assume pm2mpfo.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpfo.x: |- X = ( var1 ` A )
  assume pm2mpfo.a: |- A = ( N Mat R )
  assume pm2mpfo.q: |- Q = ( Poly1 ` A )

  disjoint A k
  disjoint B k
  disjoint M k
  disjoint N k
  disjoint Q k
  disjoint R k
  disjoint .* k
  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( k e. NN0 |-> ( ( M decompPMat k ) .* ( k .^ X ) ) ) finSupp ( 0g ` Q ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cA
    cbs
    cfv
    #
    cn0
    cQ
    cA
    cM
    vk
    cv
    #
    cdecpmat
    co
    #
    vk
    c.as
    cQ
    cbs
    cfv
    #
    cvv
    @5
    cX
    c.ex
    co
    #
    cQ
    c0g
    cfv
    #
    cA
    c0g
    cfv
    #
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @3
    cA
    crg
    wcel
    #
    cQ
    clmod
    wcel
    @0
    @1
    @11
    @2
    cA
    cR
    cN
    pm2mpfo.a
    matring
    3adant3
    #
    cQ
    cA
    pm2mpfo.q
    ply1lmod
    syl
    @3
    @11
    cA
    cQ
    csca
    cfv
    wceq
    @12
    cQ
    cA
    crg
    pm2mpfo.q
    ply1sca
    syl
    @7
    eqid
    #
    @3
    @5
    cn0
    wcel
    #
    wa
    @1
    @2
    @14
    @6
    @4
    wcel
    @0
    @1
    @2
    @14
    simpl2
    @0
    @1
    @2
    @14
    simpl3
    @3
    @14
    simpr
    cA
    cB
    cC
    @4
    cP
    cR
    @5
    cM
    cN
    crg
    pm2mpfo.p
    pm2mpfo.c
    pm2mpfo.b
    pm2mpfo.a
    @4
    eqid
    decpmatcl
    syl3anc
    @3
    @11
    @14
    @8
    @7
    wcel
    @12
    @7
    @5
    cQ
    cA
    c.ex
    cQ
    cmgp
    cfv
    #
    cX
    pm2mpfo.q
    pm2mpfo.x
    @15
    eqid
    pm2mpfo.e
    @13
    ply1moncl
    sylan
    @9
    eqid
    @10
    eqid
    #
    pm2mpfo.m
    @1
    @2
    vk
    cn0
    @6
    cmpt
    @10
    cfsupp
    wbr
    @0
    cA
    cB
    cC
    cP
    cR
    vk
    cM
    cN
    @10
    pm2mpfo.p
    pm2mpfo.c
    pm2mpfo.b
    pm2mpfo.a
    @16
    decpmatfsupp
    3adant1
    mptscmfsupp0
end
