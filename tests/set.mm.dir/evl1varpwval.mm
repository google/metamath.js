include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "evl1vard.mm"
include "cmg.mm"
include "cmgp.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "evl1expd.mm"
include "simprd.mm"

theorem evl1varpwval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
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
  assume evl1varpwval.c: |- ( ph -> C e. B )
  assume evl1varpwval.h: |- H = ( mulGrp ` R )
  assume evl1varpwval.e: |- E = ( .g ` H )


  assert |- ( ph -> ( ( Q ` ( N .^ X ) ) ` C ) = ( N E C ) )

  proof
    wph
    cN
    cX
    c.ex
    co
    #
    cW
    cbs
    cfv
    #
    wcel
    cC
    @0
    cQ
    cfv
    cfv
    cN
    cC
    cE
    co
    wceq
    wph
    cB
    cW
    cR
    c.ex
    @1
    cE
    cX
    cN
    cQ
    cC
    cC
    evl1varpw.q
    evl1varpw.w
    evl1varpw.b
    @1
    eqid
    #
    evl1varpw.r
    evl1varpwval.c
    wph
    cB
    cW
    cR
    @1
    cQ
    cX
    cC
    evl1varpw.q
    evl1varpw.x
    evl1varpw.b
    evl1varpw.w
    @2
    evl1varpw.r
    evl1varpwval.c
    evl1vard
    c.ex
    cG
    cmg
    cfv
    cW
    cmgp
    cfv
    #
    cmg
    cfv
    evl1varpw.e
    cG
    @3
    cmg
    evl1varpw.g
    fveq2i
    eqtri
    cE
    cH
    cmg
    cfv
    cR
    cmgp
    cfv
    #
    cmg
    cfv
    evl1varpwval.e
    cH
    @4
    cmg
    evl1varpwval.h
    fveq2i
    eqtri
    evl1varpw.n
    evl1expd
    simprd
end
