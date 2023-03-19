include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccom.mm"
include "cfv.mm"
include "cnvco.mm"
include "cocnvcnv1.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "wceq.mm"
include "simp1.mm"
include "ltrncnv.mm"
include "3adant2.mm"
include "ltrnco.mm"
include "syld3an3.mm"
include "trlcnv.mm"
include "syl2anc.mm"
include "syl5reqr.mm"

theorem trlcocnv
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume trlcocnv.h: |- H = ( LHyp ` K )
  assume trlcocnv.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcocnv.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( R ` ( F o. `' G ) ) = ( R ` ( G o. `' F ) ) )

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
    w3a
    #
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    cF
    cG
    ccnv
    #
    ccom
    #
    ccnv
    #
    cR
    cfv
    #
    @7
    cR
    cfv
    #
    @8
    @5
    cR
    @8
    @6
    ccnv
    @4
    ccom
    @5
    cF
    @6
    cnvco
    cG
    @4
    cocnvcnv1
    eqtri
    fveq2i
    @3
    @0
    @7
    cT
    wcel
    #
    @9
    @10
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    @6
    cT
    wcel
    #
    @11
    @0
    @2
    @12
    @1
    cT
    cG
    cH
    cK
    cW
    trlcocnv.h
    trlcocnv.t
    ltrncnv
    3adant2
    cT
    cF
    @6
    cH
    cK
    cW
    trlcocnv.h
    trlcocnv.t
    ltrnco
    syld3an3
    cR
    cT
    @7
    cH
    cK
    cW
    trlcocnv.h
    trlcocnv.t
    trlcocnv.r
    trlcnv
    syl2anc
    syl5reqr
end
