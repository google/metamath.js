include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "simp3.mm"
include "simp2l.mm"
include "simp2r.mm"
include "lhp2atnle.mm"
include "syl311anc.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp13.mm"
include "simp2rl.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simpr.mm"
include "breqtrrd.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem lhp2atne
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume lhp2atnle.l: |- .<_ = ( le ` K )
  assume lhp2atnle.j: |- .\/ = ( join ` K )
  assume lhp2atnle.a: |- A = ( Atoms ` K )
  assume lhp2atnle.h: |- H = ( LHyp ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( U e. A /\ U .<_ W ) /\ ( V e. A /\ V .<_ W ) ) /\ U =/= V ) -> ( P .\/ U ) =/= ( Q .\/ V ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cU
    cA
    wcel
    cU
    cW
    c.le
    wbr
    wa
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    cU
    cV
    wne
    #
    w3a
    #
    cV
    cP
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @13
    cQ
    cV
    c.or
    co
    #
    wne
    @12
    @2
    @3
    @11
    @6
    @9
    @15
    @2
    @3
    @4
    @10
    @11
    simp11
    @2
    @3
    @4
    @10
    @11
    simp12
    @5
    @10
    @11
    simp3
    @5
    @6
    @9
    @11
    simp2l
    @5
    @6
    @9
    @11
    simp2r
    cA
    cP
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    lhp2atnle.l
    lhp2atnle.j
    lhp2atnle.a
    lhp2atnle.h
    lhp2atnle
    syl311anc
    @12
    @14
    @13
    @16
    @12
    @13
    @16
    wceq
    #
    @14
    @12
    @17
    wa
    cV
    @16
    @13
    c.le
    @12
    cV
    @16
    c.le
    wbr
    #
    @17
    @12
    @0
    @4
    @7
    @18
    @0
    @1
    @3
    @4
    @10
    @11
    simp11l
    @2
    @3
    @4
    @10
    @11
    simp13
    @7
    @8
    @6
    @5
    @11
    simp2rl
    cA
    cQ
    cV
    c.or
    cK
    c.le
    lhp2atnle.l
    lhp2atnle.j
    lhp2atnle.a
    hlatlej2
    syl3anc
    adantr
    @12
    @17
    simpr
    breqtrrd
    ex
    necon3bd
    mpd
end
