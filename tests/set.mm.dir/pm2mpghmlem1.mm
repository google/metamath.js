include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cn0.mm"
include "wa.mm"
include "cdecpmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "matring.mm"
include "3adant3.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "eqid.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "cmgp.mm"
include "ply1tmcl.mm"

theorem pm2mpghmlem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
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
  assume pm2mpfo.l: |- L = ( Base ` Q )


  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ K e. NN0 ) -> ( ( M decompPMat K ) .* ( K .^ X ) ) e. L )

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
    cK
    cn0
    wcel
    #
    wa
    #
    cA
    crg
    wcel
    #
    cM
    cK
    cdecpmat
    co
    #
    cA
    cbs
    cfv
    #
    wcel
    #
    @4
    @7
    cK
    cX
    c.ex
    co
    c.as
    co
    cL
    wcel
    @3
    @6
    @4
    @0
    @1
    @6
    @2
    cA
    cR
    cN
    pm2mpfo.a
    matring
    3adant3
    adantr
    @5
    @1
    @2
    @4
    @9
    @0
    @1
    @2
    @4
    simpl2
    @0
    @1
    @2
    @4
    simpl3
    @3
    @4
    simpr
    #
    cA
    cB
    cC
    @8
    cP
    cR
    cK
    cM
    cN
    crg
    pm2mpfo.p
    pm2mpfo.c
    pm2mpfo.b
    pm2mpfo.a
    @8
    eqid
    #
    decpmatcl
    syl3anc
    @10
    cL
    @7
    cK
    cQ
    cA
    c.as
    c.ex
    @8
    cQ
    cmgp
    cfv
    #
    cX
    @11
    pm2mpfo.q
    pm2mpfo.x
    pm2mpfo.m
    @12
    eqid
    pm2mpfo.e
    pm2mpfo.l
    ply1tmcl
    syl3anc
end
