include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "3noncolr1N.mm"
include "simprd.mm"
include "3expia.mm"
include "islpln2ah.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "3adant3r2.mm"
include "breq2d.mm"
include "notbid.mm"
include "3imtr4d.mm"
include "3impia.mm"

theorem lplnribN
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


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ Y e. P ) -> -. R .<_ ( Q .\/ S ) )

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
    cR
    cQ
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @0
    @4
    wa
    #
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
    cR
    cS
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @5
    @8
    @0
    @4
    @10
    @13
    @0
    @4
    @10
    w3a
    cS
    cQ
    wne
    @13
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
    3noncolr1N
    simprd
    3expia
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
    @9
    @7
    @12
    @9
    @6
    @11
    cR
    c.le
    @0
    @1
    @3
    @6
    @11
    wceq
    @2
    cA
    c.or
    cK
    cQ
    cS
    islpln2a.j
    islpln2a.a
    hlatjcom
    3adant3r2
    breq2d
    notbid
    3imtr4d
    3impia
end
