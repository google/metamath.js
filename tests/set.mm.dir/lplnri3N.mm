include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "simp23.mm"
include "eqid.mm"
include "lplnribN.mm"
include "atnlej2.mm"
include "syl131anc.mm"

theorem lplnri3N
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


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ Y e. P ) -> R =/= S )

  proof
    cK
    chlt
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    w3a
    #
    cY
    cP
    wcel
    #
    w3a
    @0
    @2
    @1
    @3
    cR
    cQ
    cS
    c.or
    co
    cK
    cple
    cfv
    #
    wbr
    wn
    cR
    cS
    wne
    @0
    @4
    @5
    simp1
    @0
    @1
    @2
    @3
    @5
    simp22
    @0
    @1
    @2
    @3
    @5
    simp21
    @0
    @1
    @2
    @3
    @5
    simp23
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    @6
    cY
    @6
    eqid
    #
    lplnri1.j
    lplnri1.a
    lplnri1.p
    lplnri1.y
    lplnribN
    cA
    cR
    cQ
    cS
    c.or
    cK
    @6
    @7
    lplnri1.j
    lplnri1.a
    atnlej2
    syl131anc
end
