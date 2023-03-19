include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "simp3r.mm"
include "wi.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "simp21.mm"
include "simp3l.mm"
include "necomd.mm"
include "hlatexch1.mm"
include "syl131anc.mm"
include "mtod.mm"

theorem 4atlem0ae
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


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> -. Q .<_ ( P .\/ R ) )

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
    cP
    cQ
    wne
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cQ
    cP
    cR
    c.or
    co
    c.le
    wbr
    #
    @6
    @0
    @4
    @5
    @7
    simp3r
    @9
    @0
    @2
    @3
    @1
    cQ
    cP
    wne
    @10
    @6
    wi
    @0
    @4
    @8
    simp1
    @0
    @1
    @2
    @3
    @8
    simp22
    @0
    @1
    @2
    @3
    @8
    simp23
    @0
    @1
    @2
    @3
    @8
    simp21
    @9
    cP
    cQ
    @0
    @4
    @5
    @7
    simp3l
    necomd
    cA
    cQ
    cR
    cP
    c.or
    cK
    c.le
    4at.l
    4at.j
    4at.a
    hlatexch1
    syl131anc
    mtod
end
