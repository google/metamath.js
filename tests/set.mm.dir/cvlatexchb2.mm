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
include "simp22.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp23.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "simp21.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"

theorem cvlatexchb2
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


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ P =/= R ) -> ( P .<_ ( Q .\/ R ) <-> ( P .\/ R ) = ( Q .\/ R ) ) )

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
    c.or
    co
    #
    @9
    wceq
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
    @9
    @7
    cP
    c.le
    @6
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
    @12
    wcel
    #
    @9
    @7
    wceq
    @0
    @4
    @11
    @5
    cK
    cvllat
    3ad2ant1
    #
    @6
    @2
    @13
    @0
    @1
    @2
    @3
    @5
    simp22
    cA
    @12
    cQ
    cK
    @12
    eqid
    #
    cvlatexch.a
    atbase
    syl
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
    @12
    cR
    cK
    @16
    cvlatexch.a
    atbase
    syl
    #
    @12
    c.or
    cK
    cQ
    cR
    @16
    cvlatexch.j
    latjcom
    syl3anc
    #
    breq2d
    @6
    @10
    @8
    @9
    @7
    @6
    @11
    cP
    @12
    wcel
    #
    @14
    @10
    @8
    wceq
    @15
    @6
    @1
    @19
    @0
    @1
    @2
    @3
    @5
    simp21
    cA
    @12
    cP
    cK
    @16
    cvlatexch.a
    atbase
    syl
    @17
    @12
    c.or
    cK
    cP
    cR
    @16
    cvlatexch.j
    latjcom
    syl3anc
    @18
    eqeq12d
    3bitr4d
end
