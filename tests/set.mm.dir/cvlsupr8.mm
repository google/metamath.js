include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "cvllat.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp23.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "cvlsupr7.mm"
include "3eqtr4rd.mm"

theorem cvlsupr8
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume cvlsupr5.a: |- A = ( Atoms ` K )
  assume cvlsupr5.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ ( P .\/ R ) = ( Q .\/ R ) ) ) -> ( P .\/ Q ) = ( P .\/ R ) )

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
    @7
    cR
    cQ
    c.or
    co
    #
    @6
    cP
    cQ
    c.or
    co
    @10
    cK
    clat
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @13
    wcel
    #
    @7
    @11
    wceq
    @0
    @4
    @12
    @9
    cK
    cvllat
    3ad2ant1
    @10
    @2
    @14
    @0
    @1
    @2
    @3
    @9
    simp22
    cA
    @13
    cQ
    cK
    @13
    eqid
    #
    cvlsupr5.a
    atbase
    syl
    @10
    @3
    @15
    @0
    @1
    @2
    @3
    @9
    simp23
    cA
    @13
    cR
    cK
    @16
    cvlsupr5.a
    atbase
    syl
    @13
    c.or
    cK
    cQ
    cR
    @16
    cvlsupr5.j
    latjcom
    syl3anc
    @0
    @4
    @5
    @8
    simp3r
    cA
    cP
    cQ
    cR
    c.or
    cK
    cvlsupr5.a
    cvlsupr5.j
    cvlsupr7
    3eqtr4rd
end
