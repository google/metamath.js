include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "simp22.mm"
include "4atlem0ae.mm"
include "2llnma1.mm"
include "syl131anc.mm"

theorem 2llnma2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume 2llnm.l: |- .<_ = ( le ` K )
  assume 2llnm.j: |- .\/ = ( join ` K )
  assume 2llnm.m: |- ./\ = ( meet ` K )
  assume 2llnm.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> ( ( R .\/ P ) ./\ ( R .\/ Q ) ) = R )

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
    @0
    @1
    @3
    @2
    cQ
    cP
    cR
    c.or
    co
    c.le
    wbr
    wn
    cR
    cP
    c.or
    co
    cR
    cQ
    c.or
    co
    c.an
    co
    cR
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
    simp21
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
    simp22
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    2llnm.l
    2llnm.j
    2llnm.a
    4atlem0ae
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    c.an
    2llnm.l
    2llnm.j
    2llnm.m
    2llnm.a
    2llnma1
    syl131anc
end
