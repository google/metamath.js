include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "simp3.mm"
include "wceq.mm"
include "trlcnv.mm"
include "neeqtrrd.mm"
include "trlcoat.mm"
include "syl121anc.mm"

theorem trlcocnvat
  let cA: class A
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume trlcoat.a: |- A = ( Atoms ` K )
  assume trlcoat.h: |- H = ( LHyp ` K )
  assume trlcoat.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcoat.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( R ` F ) =/= ( R ` G ) ) -> ( R ` ( F o. `' G ) ) e. A )

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
    cG
    cT
    wcel
    #
    wa
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    @0
    @1
    cG
    ccnv
    #
    cT
    wcel
    #
    @4
    @8
    cR
    cfv
    #
    wne
    cF
    @8
    ccom
    cR
    cfv
    cA
    wcel
    @0
    @3
    @6
    simp1
    #
    @0
    @1
    @2
    @6
    simp2l
    @7
    @0
    @2
    @9
    @11
    @0
    @1
    @2
    @6
    simp2r
    #
    cT
    cG
    cH
    cK
    cW
    trlcoat.h
    trlcoat.t
    ltrncnv
    syl2anc
    @7
    @4
    @5
    @10
    @0
    @3
    @6
    simp3
    @7
    @0
    @2
    @10
    @5
    wceq
    @11
    @12
    cR
    cT
    cG
    cH
    cK
    cW
    trlcoat.h
    trlcoat.t
    trlcoat.r
    trlcnv
    syl2anc
    neeqtrrd
    cA
    cR
    cT
    cF
    @8
    cH
    cK
    cW
    trlcoat.a
    trlcoat.h
    trlcoat.t
    trlcoat.r
    trlcoat
    syl121anc
end
