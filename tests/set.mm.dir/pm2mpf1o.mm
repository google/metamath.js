include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "pm2mpf1.mm"
include "pm2mpfo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem pm2mpf1o
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : B -1-1-onto-> L )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    cB
    cL
    cT
    wf1
    cB
    cL
    cT
    wfo
    cB
    cL
    cT
    wf1o
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
    pm2mpf1
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
    pm2mpfo
    cB
    cL
    cT
    df-f1o
    sylanbrc
end
