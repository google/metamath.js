include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp11.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp12.mm"
include "4noncolr3.mm"
include "syl321anc.mm"

theorem 4noncolr2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3noncol.l: |- .<_ = ( le ` K )
  assume 3noncol.j: |- .\/ = ( join ` K )
  assume 3noncol.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( R =/= S /\ -. P .<_ ( R .\/ S ) /\ -. Q .<_ ( ( R .\/ S ) .\/ P ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cS
    @7
    cR
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    w3a
    @0
    @2
    @4
    @5
    @1
    cQ
    cR
    wne
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    cP
    @9
    cS
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cR
    cS
    wne
    cP
    cR
    cS
    c.or
    co
    #
    c.le
    wbr
    wn
    cQ
    @10
    cP
    c.or
    co
    c.le
    wbr
    wn
    w3a
    @0
    @1
    @2
    @6
    @8
    simp11
    @0
    @1
    @2
    @6
    @8
    simp13
    @3
    @4
    @5
    @8
    simp2l
    @3
    @4
    @5
    @8
    simp2r
    @0
    @1
    @2
    @6
    @8
    simp12
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    3noncol.l
    3noncol.j
    3noncol.a
    4noncolr3
    cA
    cQ
    cR
    cS
    cP
    c.or
    cK
    c.le
    3noncol.l
    3noncol.j
    3noncol.a
    4noncolr3
    syl321anc
end
