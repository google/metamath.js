include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "simp3r.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpr.mm"
include "jca.mm"
include "simpl3l.mm"
include "ltrnatneq.mm"
include "syl131anc.mm"
include "ex.mm"
include "necon4bd.mm"
include "mpd.mm"

theorem ltrnatlw
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrn2eq.l: |- .<_ = ( le ` K )
  assume ltrn2eq.a: |- A = ( Atoms ` K )
  assume ltrn2eq.h: |- H = ( LHyp ` K )
  assume ltrn2eq.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( F ` P ) =/= P /\ ( F ` Q ) = Q ) ) -> Q .<_ W )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
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
    cP
    cF
    cfv
    cP
    wne
    #
    cQ
    cF
    cfv
    #
    cQ
    wceq
    #
    wa
    #
    w3a
    #
    @7
    cQ
    cW
    c.le
    wbr
    #
    @0
    @4
    @5
    @7
    simp3r
    @9
    @10
    @6
    cQ
    @9
    @10
    wn
    #
    @6
    cQ
    wne
    #
    @9
    @11
    wa
    #
    @0
    @1
    @2
    @3
    @11
    wa
    @5
    @12
    @0
    @4
    @8
    @11
    simpl1
    @1
    @2
    @3
    @0
    @8
    @11
    simpl21
    @1
    @2
    @3
    @0
    @8
    @11
    simpl22
    @13
    @3
    @11
    @1
    @2
    @3
    @0
    @8
    @11
    simpl23
    @9
    @11
    simpr
    jca
    @5
    @7
    @0
    @4
    @11
    simpl3l
    cA
    cP
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    ltrn2eq.l
    ltrn2eq.a
    ltrn2eq.h
    ltrn2eq.t
    ltrnatneq
    syl131anc
    ex
    necon4bd
    mpd
end
