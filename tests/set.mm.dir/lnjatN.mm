include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "lnatexN.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp1rl.mm"
include "simp1l3.mm"
include "simp2.mm"
include "necomd.mm"
include "simp1rr.mm"
include "simp3r.mm"
include "lneq2at.mm"
include "syl332anc.mm"
include "jca.mm"
include "3exp.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem lnjatN
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let vq: setvar q
  assume lnjat.b: |- B = ( Base ` K )
  assume lnjat.l: |- .<_ = ( le ` K )
  assume lnjat.j: |- .\/ = ( join ` K )
  assume lnjat.a: |- A = ( Atoms ` K )
  assume lnjat.n: |- N = ( Lines ` K )
  assume lnjat.m: |- M = ( pmap ` K )

  disjoint A q
  disjoint B q
  disjoint K q
  disjoint .<_ q
  disjoint M q
  disjoint N q
  disjoint P q
  disjoint X q
  assert |- ( ( ( K e. HL /\ X e. B /\ P e. A ) /\ ( ( M ` X ) e. N /\ P .<_ X ) ) -> E. q e. A ( q =/= P /\ X = ( P .\/ q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cM
    cfv
    cN
    wcel
    #
    cP
    cX
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vq
    cv
    #
    cP
    wne
    #
    @8
    cX
    c.le
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    #
    @9
    cX
    cP
    @8
    c.or
    co
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    @7
    @0
    @1
    @4
    @12
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl2
    @3
    @4
    @5
    simprl
    cA
    cB
    cP
    cK
    c.le
    cM
    cN
    cX
    vq
    lnjat.b
    lnjat.l
    lnjat.a
    lnjat.n
    lnjat.m
    lnatexN
    syl3anc
    @7
    @11
    @14
    vq
    cA
    @7
    @8
    cA
    wcel
    #
    @11
    @14
    @7
    @15
    @11
    w3a
    #
    @9
    @13
    @7
    @15
    @9
    @10
    simp3l
    #
    @16
    @0
    @1
    @4
    @2
    @15
    cP
    @8
    wne
    @5
    @10
    @13
    @0
    @1
    @2
    @6
    @15
    @11
    simp1l1
    @0
    @1
    @2
    @6
    @15
    @11
    simp1l2
    @4
    @5
    @3
    @15
    @11
    simp1rl
    @0
    @1
    @2
    @6
    @15
    @11
    simp1l3
    @7
    @15
    @11
    simp2
    @16
    @8
    cP
    @17
    necomd
    @4
    @5
    @3
    @15
    @11
    simp1rr
    @7
    @15
    @9
    @10
    simp3r
    cA
    cB
    cP
    @8
    c.or
    cK
    c.le
    cM
    cN
    cX
    lnjat.b
    lnjat.l
    lnjat.j
    lnjat.a
    lnjat.n
    lnjat.m
    lneq2at
    syl332anc
    jca
    3exp
    reximdvai
    mpd
end
