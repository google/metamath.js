include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "simp1.mm"
include "simp23.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3.mm"
include "atnlej1.mm"
include "necomd.mm"
include "syl131anc.mm"

theorem 4atlem0be
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ -. R .<_ ( P .\/ Q ) ) -> P =/= R )

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
    cR
    cA
    wcel
    #
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    @0
    @3
    @1
    @2
    @5
    cP
    cR
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
    simp23
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
    simp22
    @0
    @4
    @5
    simp3
    @0
    @3
    @1
    @2
    w3a
    @5
    w3a
    cR
    cP
    cA
    cR
    cP
    cQ
    c.or
    cK
    c.le
    4at.l
    4at.j
    4at.a
    atnlej1
    necomd
    syl131anc
end
