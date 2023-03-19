include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp2.mm"
include "eqid.mm"
include "trlval2.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "ltrnat.mm"
include "simp3r.mm"
include "necomd.mm"
include "lhpat.mm"
include "syl112anc.mm"
include "eqeltrd.mm"

theorem trlat
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume trlat.l: |- .<_ = ( le ` K )
  assume trlat.a: |- A = ( Atoms ` K )
  assume trlat.h: |- H = ( LHyp ` K )
  assume trlat.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlat.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( F e. T /\ ( F ` P ) =/= P ) ) -> ( R ` F ) e. A )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cF
    cT
    wcel
    #
    cP
    cF
    cfv
    #
    cP
    wne
    #
    wa
    #
    w3a
    #
    cF
    cR
    cfv
    #
    cP
    @5
    cK
    cjn
    cfv
    #
    co
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cA
    @8
    @0
    @4
    @3
    @9
    @12
    wceq
    @0
    @3
    @7
    simp1
    #
    @0
    @3
    @4
    @6
    simp3l
    #
    @0
    @3
    @7
    simp2
    #
    cA
    cP
    cR
    cT
    cF
    cH
    @10
    cK
    c.le
    @11
    cW
    trlat.l
    @10
    eqid
    #
    @11
    eqid
    #
    trlat.a
    trlat.h
    trlat.t
    trlat.r
    trlval2
    syl3anc
    @8
    @0
    @3
    @5
    cA
    wcel
    #
    cP
    @5
    wne
    @12
    cA
    wcel
    @13
    @15
    @8
    @0
    @4
    @1
    @18
    @13
    @14
    @0
    @1
    @2
    @7
    simp2l
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    trlat.l
    trlat.a
    trlat.h
    trlat.t
    ltrnat
    syl3anc
    @8
    @5
    cP
    @0
    @3
    @4
    @6
    simp3r
    necomd
    cA
    cP
    @5
    cH
    @10
    cK
    c.le
    @11
    cW
    trlat.l
    @16
    @17
    trlat.a
    trlat.h
    lhpat
    syl112anc
    eqeltrd
end
