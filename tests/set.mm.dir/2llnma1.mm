include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "mtbid.mm"
include "2llnma1b.mm"
include "syl131anc.mm"

theorem 2llnma1
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


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ -. R .<_ ( P .\/ Q ) ) -> ( ( Q .\/ P ) ./\ ( Q .\/ R ) ) = Q )

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
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    @3
    cR
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @11
    cQ
    cR
    c.or
    co
    c.an
    co
    cQ
    wceq
    @0
    @4
    @7
    simp1
    #
    @8
    @1
    @10
    @0
    @1
    @2
    @3
    @7
    simp21
    #
    cA
    @9
    cP
    cK
    @9
    eqid
    #
    2llnm.a
    atbase
    syl
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    @0
    @1
    @2
    @3
    @7
    simp23
    @8
    @6
    @12
    @0
    @4
    @7
    simp3
    @8
    @5
    @11
    cR
    c.le
    @8
    @0
    @1
    @2
    @5
    @11
    wceq
    @13
    @14
    @16
    cA
    c.or
    cK
    cP
    cQ
    2llnm.j
    2llnm.a
    hlatjcom
    syl3anc
    breq2d
    mtbid
    cA
    @9
    cQ
    cR
    c.or
    cK
    c.le
    c.an
    cP
    @15
    2llnm.l
    2llnm.j
    2llnm.m
    2llnm.a
    2llnma1b
    syl131anc
end
