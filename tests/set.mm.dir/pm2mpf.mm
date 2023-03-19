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
include "cvv.mm"
include "ovexd.mm"
include "pm2mpval.mm"
include "cfv.mm"
include "pm2mpcl.mm"
include "3expa.mm"
include "fmpt2d.mm"

theorem pm2mpf
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
  let vk: setvar k
  let vb: setvar b
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let cV: class V
  let va: setvar a
  let vq: setvar q
  let cM: class M
  assume pm2mpval.p: |- P = ( Poly1 ` R )
  assume pm2mpval.c: |- C = ( N Mat P )
  assume pm2mpval.b: |- B = ( Base ` C )
  assume pm2mpval.m: |- .* = ( .s ` Q )
  assume pm2mpval.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpval.x: |- X = ( var1 ` A )
  assume pm2mpval.a: |- A = ( N Mat R )
  assume pm2mpval.q: |- Q = ( Poly1 ` A )
  assume pm2mpval.t: |- T = ( N pMatToMatPoly R )
  assume pm2mpcl.l: |- L = ( Base ` Q )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : B --> L )

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
    vm
    vb
    cB
    cQ
    vk
    cn0
    vm
    cv
    #
    vk
    cv
    #
    cdecpmat
    co
    @4
    cX
    c.ex
    co
    c.as
    co
    cmpt
    #
    cgsu
    co
    cL
    cT
    cvv
    @2
    @3
    cB
    wcel
    wa
    cQ
    @5
    cgsu
    ovexd
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    vk
    vm
    c.ex
    c.as
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
    pm2mpval
    @0
    @1
    vb
    cv
    #
    cB
    wcel
    @6
    cT
    cfv
    cL
    wcel
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
    @6
    cN
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
    pm2mpcl.l
    pm2mpcl
    3expa
    fmpt2d
end
