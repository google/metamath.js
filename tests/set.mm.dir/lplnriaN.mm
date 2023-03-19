include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "islpln2ah.mm"
include "hlatcon3.mm"
include "3expia.mm"
include "sylbid.mm"
include "3impia.mm"

theorem lplnriaN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cY: class Y
  assume islpln2a.l: |- .<_ = ( le ` K )
  assume islpln2a.j: |- .\/ = ( join ` K )
  assume islpln2a.a: |- A = ( Atoms ` K )
  assume islpln2a.p: |- P = ( LPlanes ` K )
  assume islpln2a.y: |- Y = ( ( Q .\/ R ) .\/ S )


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ Y e. P ) -> -. Q .<_ ( R .\/ S ) )

  proof
    cK
    chlt
    wcel
    #
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
    #
    cY
    cP
    wcel
    #
    cQ
    cR
    cS
    c.or
    co
    c.le
    wbr
    wn
    #
    @0
    @1
    wa
    @2
    cQ
    cR
    wne
    cS
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    wa
    #
    @3
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    cY
    islpln2a.l
    islpln2a.j
    islpln2a.a
    islpln2a.p
    islpln2a.y
    islpln2ah
    @0
    @1
    @4
    @3
    cA
    cQ
    cR
    cS
    c.or
    cK
    c.le
    islpln2a.l
    islpln2a.j
    islpln2a.a
    hlatcon3
    3expia
    sylbid
    3impia
end
