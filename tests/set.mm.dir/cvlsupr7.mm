include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "clat.mm"
include "cbs.mm"
include "cvllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp23.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "breqtrd.mm"
include "simp22.mm"
include "latjcom.mm"
include "wb.mm"
include "simp1.mm"
include "simp3l.mm"
include "cvlatexchb2.mm"
include "syl131anc.mm"
include "mpbid.mm"

theorem cvlsupr7
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume cvlsupr5.a: |- A = ( Atoms ` K )
  assume cvlsupr5.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ ( P .\/ R ) = ( Q .\/ R ) ) ) -> ( P .\/ Q ) = ( R .\/ Q ) )

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
    c.or
    co
    #
    cQ
    cR
    c.or
    co
    #
    wceq
    #
    wa
    #
    w3a
    #
    cP
    cR
    cQ
    c.or
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    cP
    cQ
    c.or
    co
    @11
    wceq
    #
    @10
    cP
    @7
    @11
    @12
    @10
    cP
    @6
    @7
    @12
    @10
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
    cR
    @16
    wcel
    #
    cP
    @6
    @12
    wbr
    @0
    @4
    @15
    @9
    cK
    cvllat
    3ad2ant1
    #
    @10
    @1
    @17
    @0
    @1
    @2
    @3
    @9
    simp21
    #
    cA
    @16
    cP
    cK
    @16
    eqid
    #
    cvlsupr5.a
    atbase
    syl
    @10
    @3
    @18
    @0
    @1
    @2
    @3
    @9
    simp23
    #
    cA
    @16
    cR
    cK
    @21
    cvlsupr5.a
    atbase
    syl
    #
    @16
    c.or
    cK
    @12
    cP
    cR
    @21
    @12
    eqid
    #
    cvlsupr5.j
    latlej1
    syl3anc
    @0
    @4
    @5
    @8
    simp3r
    breqtrd
    @10
    @15
    cQ
    @16
    wcel
    #
    @18
    @7
    @11
    wceq
    @19
    @10
    @2
    @25
    @0
    @1
    @2
    @3
    @9
    simp22
    #
    cA
    @16
    cQ
    cK
    @21
    cvlsupr5.a
    atbase
    syl
    @23
    @16
    c.or
    cK
    cQ
    cR
    @21
    cvlsupr5.j
    latjcom
    syl3anc
    breqtrd
    @10
    @0
    @1
    @3
    @2
    @5
    @13
    @14
    wb
    @0
    @4
    @9
    simp1
    @20
    @22
    @26
    @0
    @4
    @5
    @8
    simp3l
    cA
    cP
    cR
    cQ
    c.or
    cK
    @12
    @24
    cvlsupr5.j
    cvlsupr5.a
    cvlatexchb2
    syl131anc
    mpbid
end
