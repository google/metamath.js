include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "hlatcon3.mm"
include "wceq.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "mtbid.mm"

theorem hlatcon2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3noncol.l: |- .<_ = ( le ` K )
  assume 3noncol.j: |- .\/ = ( join ` K )
  assume 3noncol.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> -. P .<_ ( R .\/ Q ) )

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
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    3noncol.l
    3noncol.j
    3noncol.a
    hlatcon3
    @6
    @7
    @8
    cP
    c.le
    @6
    @0
    @2
    @3
    @7
    @8
    wceq
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
    simp23
    cA
    c.or
    cK
    cQ
    cR
    3noncol.j
    3noncol.a
    hlatjcom
    syl3anc
    breq2d
    mtbid
end
