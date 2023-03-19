include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "co.mm"
include "pmatlmod.mm"
include "eqid.mm"
include "vr1cl.mm"
include "adantl.mm"
include "wceq.mm"
include "ply1ring.mm"
include "matsca2.mm"
include "sylan2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "pmatring.mm"
include "ringidcl.mm"
include "syl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"

theorem chpdmatlem0
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume chpdmat.c: |- C = ( N CharPlyMat R )
  assume chpdmat.p: |- P = ( Poly1 ` R )
  assume chpdmat.a: |- A = ( N Mat R )
  assume chpdmat.s: |- S = ( algSc ` P )
  assume chpdmat.b: |- B = ( Base ` A )
  assume chpdmat.x: |- X = ( var1 ` R )
  assume chpdmat.0: |- .0. = ( 0g ` R )
  assume chpdmat.g: |- G = ( mulGrp ` P )
  assume chpdmat.m: |- .- = ( -g ` P )
  assume chpdmatlem.q: |- Q = ( N Mat P )
  assume chpdmatlem.1: |- .1. = ( 1r ` Q )
  assume chpdmatlem.m: |- .x. = ( .s ` Q )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( X .x. .1. ) e. ( Base ` Q ) )

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
    cQ
    clmod
    wcel
    cX
    cQ
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    c.1
    cQ
    cbs
    cfv
    #
    wcel
    #
    cX
    c.1
    c.x
    co
    @5
    wcel
    cQ
    cP
    cR
    cN
    chpdmat.p
    chpdmatlem.q
    pmatlmod
    @2
    cX
    cP
    cbs
    cfv
    #
    @4
    @1
    cX
    @7
    wcel
    @0
    @7
    cP
    cR
    cX
    chpdmat.x
    chpdmat.p
    @7
    eqid
    vr1cl
    adantl
    @2
    @3
    cP
    cbs
    @2
    cP
    @3
    @1
    @0
    cP
    crg
    wcel
    cP
    @3
    wceq
    cP
    cR
    chpdmat.p
    ply1ring
    cQ
    cP
    cN
    crg
    chpdmatlem.q
    matsca2
    sylan2
    eqcomd
    fveq2d
    eleqtrrd
    @2
    cQ
    crg
    wcel
    @6
    cQ
    cP
    cR
    cN
    chpdmat.p
    chpdmatlem.q
    pmatring
    @5
    cQ
    c.1
    @5
    eqid
    #
    chpdmatlem.1
    ringidcl
    syl
    cX
    c.x
    @3
    @4
    @5
    cQ
    c.1
    @8
    @3
    eqid
    chpdmatlem.m
    @4
    eqid
    lmodvscl
    syl3anc
end
