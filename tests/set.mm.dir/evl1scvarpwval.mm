include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "cmnd.mm"
include "cn0.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "evl1varpwval.mm"
include "jca.mm"
include "evl1vsd.mm"
include "simprd.mm"

theorem evl1scvarpwval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let cN: class N
  let cW: class W
  let cX: class X
  assume evl1varpw.q: |- Q = ( eval1 ` R )
  assume evl1varpw.w: |- W = ( Poly1 ` R )
  assume evl1varpw.g: |- G = ( mulGrp ` W )
  assume evl1varpw.x: |- X = ( var1 ` R )
  assume evl1varpw.b: |- B = ( Base ` R )
  assume evl1varpw.e: |- .^ = ( .g ` G )
  assume evl1varpw.r: |- ( ph -> R e. CRing )
  assume evl1varpw.n: |- ( ph -> N e. NN0 )
  assume evl1scvarpw.t1: |- .X. = ( .s ` W )
  assume evl1scvarpw.a: |- ( ph -> A e. B )
  assume evl1scvarpwval.c: |- ( ph -> C e. B )
  assume evl1scvarpwval.h: |- H = ( mulGrp ` R )
  assume evl1scvarpwval.e: |- E = ( .g ` H )
  assume evl1scvarpwval.t: |- .x. = ( .r ` R )


  assert |- ( ph -> ( ( Q ` ( A .X. ( N .^ X ) ) ) ` C ) = ( A .x. ( N E C ) ) )

  proof
    wph
    cA
    cN
    cX
    c.ex
    co
    #
    c.xp
    co
    #
    cW
    cbs
    cfv
    #
    wcel
    cC
    @1
    cQ
    cfv
    cfv
    cA
    cN
    cC
    cE
    co
    #
    c.x
    co
    wceq
    wph
    cB
    cW
    cR
    c.xp
    c.x
    @2
    @0
    cA
    cQ
    @3
    cC
    evl1varpw.q
    evl1varpw.w
    evl1varpw.b
    @2
    eqid
    #
    evl1varpw.r
    evl1scvarpwval.c
    wph
    @0
    @2
    wcel
    #
    cC
    @0
    cQ
    cfv
    cfv
    @3
    wceq
    wph
    cG
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    cX
    @2
    wcel
    #
    @5
    wph
    cW
    crg
    wcel
    #
    @6
    wph
    cR
    crg
    wcel
    #
    @8
    wph
    cR
    ccrg
    wcel
    @9
    evl1varpw.r
    cR
    crngring
    syl
    #
    cW
    cR
    evl1varpw.w
    ply1ring
    syl
    cW
    cG
    evl1varpw.g
    ringmgp
    syl
    evl1varpw.n
    wph
    @9
    @7
    @10
    @2
    cW
    cR
    cX
    evl1varpw.x
    evl1varpw.w
    @4
    vr1cl
    syl
    @2
    c.ex
    cG
    cN
    cX
    @2
    cW
    cG
    evl1varpw.g
    @4
    mgpbas
    evl1varpw.e
    mulgnn0cl
    syl3anc
    wph
    cB
    cC
    cQ
    cR
    cE
    c.ex
    cG
    cH
    cN
    cW
    cX
    evl1varpw.q
    evl1varpw.w
    evl1varpw.g
    evl1varpw.x
    evl1varpw.b
    evl1varpw.e
    evl1varpw.r
    evl1varpw.n
    evl1scvarpwval.c
    evl1scvarpwval.h
    evl1scvarpwval.e
    evl1varpwval
    jca
    evl1scvarpw.a
    evl1scvarpw.t1
    evl1scvarpwval.t
    evl1vsd
    simprd
end
