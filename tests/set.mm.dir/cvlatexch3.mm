include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "simp22.mm"
include "simp3l.mm"
include "cvlatexchb1.mm"
include "syl131anc.mm"
include "biimpa.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simpl1.mm"
include "cvllat.mm"
include "syl.mm"
include "simpl21.mm"
include "eqid.mm"
include "atbase.mm"
include "simpl22.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "cvlatexchb2.mm"
include "3adant3l.mm"
include "3eqtr4d.mm"
include "ex.mm"

theorem cvlatexch3
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


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ P =/= R ) ) -> ( P .<_ ( Q .\/ R ) -> ( P .\/ Q ) = ( P .\/ R ) ) )

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
    cQ
    wne
    #
    cP
    cR
    wne
    #
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
    #
    cP
    cQ
    c.or
    co
    #
    cP
    cR
    c.or
    co
    #
    wceq
    @8
    @10
    wa
    #
    cQ
    cP
    c.or
    co
    #
    @9
    @11
    @12
    @8
    @10
    @14
    @9
    wceq
    #
    @8
    @0
    @1
    @3
    @2
    @5
    @10
    @15
    wb
    @0
    @4
    @7
    simp1
    @0
    @1
    @2
    @3
    @7
    simp21
    @0
    @1
    @2
    @3
    @7
    simp23
    @0
    @1
    @2
    @3
    @7
    simp22
    @0
    @4
    @5
    @6
    simp3l
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    cvlatexch.l
    cvlatexch.j
    cvlatexch.a
    cvlatexchb1
    syl131anc
    biimpa
    @13
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @17
    wcel
    #
    @11
    @14
    wceq
    @13
    @0
    @16
    @0
    @4
    @7
    @10
    simpl1
    cK
    cvllat
    syl
    @13
    @1
    @18
    @1
    @2
    @3
    @0
    @7
    @10
    simpl21
    cA
    @17
    cP
    cK
    @17
    eqid
    #
    cvlatexch.a
    atbase
    syl
    @13
    @2
    @19
    @1
    @2
    @3
    @0
    @7
    @10
    simpl22
    cA
    @17
    cQ
    cK
    @20
    cvlatexch.a
    atbase
    syl
    @17
    c.or
    cK
    cP
    cQ
    @20
    cvlatexch.j
    latjcom
    syl3anc
    @8
    @10
    @12
    @9
    wceq
    #
    @0
    @4
    @6
    @10
    @21
    wb
    @5
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
    cvlatexchb2
    3adant3l
    biimpa
    3eqtr4d
    ex
end
