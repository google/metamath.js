include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "simp3ll.mm"
include "wb.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "simp3lr.mm"
include "3jca.mm"
include "exatleN.mm"
include "syld3an3.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "cal.mm"
include "simp1l.mm"
include "hlatl.mm"
include "syl.mm"
include "simp23.mm"
include "simp1r.mm"
include "atnle.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem cdlema2N
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume cdlema2.b: |- B = ( Base ` K )
  assume cdlema2.l: |- .<_ = ( le ` K )
  assume cdlema2.j: |- .\/ = ( join ` K )
  assume cdlema2.m: |- ./\ = ( meet ` K )
  assume cdlema2.z: |- .0. = ( 0. ` K )
  assume cdlema2.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ X e. B ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( ( R =/= P /\ R .<_ ( P .\/ Q ) ) /\ ( P .<_ X /\ -. Q .<_ X ) ) ) -> ( R ./\ X ) = .0. )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
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
    wne
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    cP
    cX
    c.le
    wbr
    #
    cQ
    cX
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    w3a
    #
    cR
    cX
    c.le
    wbr
    #
    wn
    #
    cR
    cX
    c.an
    co
    c.0
    wceq
    #
    @14
    @16
    @7
    @7
    @8
    @12
    @2
    @6
    simp3ll
    @14
    @15
    cR
    cP
    @2
    @6
    @13
    @10
    @11
    @8
    w3a
    @15
    cR
    cP
    wceq
    wb
    @14
    @10
    @11
    @8
    @10
    @11
    @9
    @2
    @6
    simp3rl
    @10
    @11
    @9
    @2
    @6
    simp3rr
    @7
    @8
    @12
    @2
    @6
    simp3lr
    3jca
    cA
    cB
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cX
    cdlema2.b
    cdlema2.l
    cdlema2.j
    cdlema2.a
    exatleN
    syld3an3
    necon3bbid
    mpbird
    @14
    cK
    cal
    wcel
    #
    @5
    @1
    @16
    @17
    wb
    @14
    @0
    @18
    @0
    @1
    @6
    @13
    simp1l
    cK
    hlatl
    syl
    @2
    @3
    @4
    @5
    @13
    simp23
    @0
    @1
    @6
    @13
    simp1r
    cA
    cB
    cR
    cK
    c.le
    c.an
    cX
    c.0
    cdlema2.b
    cdlema2.l
    cdlema2.m
    cdlema2.z
    cdlema2.a
    atnle
    syl3anc
    mpbid
end
