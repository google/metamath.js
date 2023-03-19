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
include "hlatjcom.mm"
include "syl3anc.mm"
include "simp22.mm"
include "oveq12d.mm"
include "2llnma2.mm"
include "eqtrd.mm"

theorem 2llnma2rN
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


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ R ) ./\ ( Q .\/ R ) ) = R )

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
    cR
    c.or
    co
    #
    cQ
    cR
    c.or
    co
    #
    c.an
    co
    cR
    cP
    c.or
    co
    #
    cR
    cQ
    c.or
    co
    #
    c.an
    co
    cR
    @6
    @7
    @9
    @8
    @10
    c.an
    @6
    @0
    @1
    @3
    @7
    @9
    wceq
    @0
    @4
    @5
    simp1
    #
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
    #
    cA
    c.or
    cK
    cP
    cR
    2llnm.j
    2llnm.a
    hlatjcom
    syl3anc
    @6
    @0
    @2
    @3
    @8
    @10
    wceq
    @11
    @0
    @1
    @2
    @3
    @5
    simp22
    @12
    cA
    c.or
    cK
    cQ
    cR
    2llnm.j
    2llnm.a
    hlatjcom
    syl3anc
    oveq12d
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    c.an
    2llnm.l
    2llnm.j
    2llnm.m
    2llnm.a
    2llnma2
    eqtrd
end
