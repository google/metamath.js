include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "cvlatexchb1.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "cvllat.mm"
include "3ad2ant1.mm"
include "simp23.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp22.mm"
include "latlej2.mm"
include "syl3anc.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"

theorem cvlatexch1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume cvlatexch.l: |- .<_ = ( le ` K )
  assume cvlatexch.j: |- .\/ = ( join ` K )
  assume cvlatexch.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ P =/= R ) -> ( P .<_ ( R .\/ Q ) -> Q .<_ ( R .\/ P ) ) )

  proof
    cK
    clc
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
    cR
    wne
    #
    w3a
    #
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    cR
    cP
    c.or
    co
    #
    @7
    wceq
    #
    cQ
    @8
    c.le
    wbr
    #
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cvlatexch.l
    cvlatexch.j
    cvlatexch.a
    cvlatexchb1
    @6
    @10
    @9
    cQ
    @7
    c.le
    wbr
    #
    @6
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @13
    wcel
    #
    @11
    @0
    @4
    @12
    @5
    cK
    cvllat
    3ad2ant1
    @6
    @3
    @14
    @0
    @1
    @2
    @3
    @5
    simp23
    cA
    @13
    cR
    cK
    @13
    eqid
    #
    cvlatexch.a
    atbase
    syl
    @6
    @2
    @15
    @0
    @1
    @2
    @3
    @5
    simp22
    cA
    @13
    cQ
    cK
    @16
    cvlatexch.a
    atbase
    syl
    @13
    c.or
    cK
    c.le
    cR
    cQ
    @16
    cvlatexch.l
    cvlatexch.j
    latlej2
    syl3anc
    @8
    @7
    cQ
    c.le
    breq2
    syl5ibrcom
    sylbid
end
