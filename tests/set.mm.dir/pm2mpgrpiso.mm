include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cgim.mm"
include "pm2mpghm.mm"
include "eqid.mm"
include "pm2mpf1o.mm"
include "isgim.mm"
include "sylanbrc.mm"

theorem pm2mpgrpiso
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
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  let vl: setvar l
  let vn: setvar n
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T e. ( C GrpIso Q ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    cT
    cC
    cQ
    cghm
    co
    wcel
    cB
    cQ
    cbs
    cfv
    #
    cT
    wf1o
    cT
    cC
    cQ
    cgim
    co
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
    pm2mpfo.l
    pm2mpfo.t
    pm2mpghm
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    c.ex
    c.as
    @0
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
    @0
    eqid
    #
    pm2mpfo.t
    pm2mpf1o
    cB
    @0
    cC
    cQ
    cT
    pm2mpfo.b
    @1
    isgim
    sylanbrc
end
