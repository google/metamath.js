include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "eqid.mm"
include "lplnriaN.mm"
include "atnlej2.mm"
include "syld3an3.mm"

theorem lplnri2N
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let cY: class Y
  assume lplnri1.j: |- .\/ = ( join ` K )
  assume lplnri1.a: |- A = ( Atoms ` K )
  assume lplnri1.p: |- P = ( LPlanes ` K )
  assume lplnri1.y: |- Y = ( ( Q .\/ R ) .\/ S )


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ Y e. P ) -> Q =/= S )

  proof
    cK
    chlt
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    cS
    cA
    wcel
    w3a
    cY
    cP
    wcel
    cQ
    cR
    cS
    c.or
    co
    cK
    cple
    cfv
    #
    wbr
    wn
    cQ
    cS
    wne
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    @0
    cY
    @0
    eqid
    #
    lplnri1.j
    lplnri1.a
    lplnri1.p
    lplnri1.y
    lplnriaN
    cA
    cQ
    cR
    cS
    c.or
    cK
    @0
    @1
    lplnri1.j
    lplnri1.a
    atnlej2
    syld3an3
end
