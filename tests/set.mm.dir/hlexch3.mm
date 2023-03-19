include "chlt.mm"
include "wcel.mm"
include "clc.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "hlcvl.mm"
include "cvlexch3.mm"
include "syl3an1.mm"

theorem hlexch3
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume hlexch3.b: |- B = ( Base ` K )
  assume hlexch3.l: |- .<_ = ( le ` K )
  assume hlexch3.j: |- .\/ = ( join ` K )
  assume hlexch3.m: |- ./\ = ( meet ` K )
  assume hlexch3.z: |- .0. = ( 0. ` K )
  assume hlexch3.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ X e. B ) /\ ( P ./\ X ) = .0. ) -> ( P .<_ ( X .\/ Q ) -> Q .<_ ( X .\/ P ) ) )

  proof
    cK
    chlt
    wcel
    cK
    clc
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cX
    cB
    wcel
    w3a
    cP
    cX
    c.an
    co
    c.0
    wceq
    cP
    cX
    cQ
    c.or
    co
    c.le
    wbr
    cQ
    cX
    cP
    c.or
    co
    c.le
    wbr
    wi
    cK
    hlcvl
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    c.an
    cX
    c.0
    hlexch3.b
    hlexch3.l
    hlexch3.j
    hlexch3.m
    hlexch3.z
    hlexch3.a
    cvlexch3
    syl3an1
end
