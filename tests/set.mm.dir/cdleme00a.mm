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
include "syl131anc.mm"

theorem cdleme00a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ -. R .<_ ( P .\/ Q ) ) -> R =/= P )

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
    cR
    cP
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
    cA
    cR
    cP
    cQ
    c.or
    cK
    c.le
    cdleme0.l
    cdleme0.j
    cdleme0.a
    atnlej1
    syl131anc
end
