include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp2.mm"
include "3jca.mm"
include "simp3.mm"
include "ctrl.mm"
include "eqid.mm"
include "cdlemj3.mm"
include "syl31anc.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "tendoeq2.mm"
include "syl221anc.mm"

theorem tendocan
  let cB: class B
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vh: setvar h
  assume tendocan.b: |- B = ( Base ` K )
  assume tendocan.h: |- H = ( LHyp ` K )
  assume tendocan.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendocan.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ ( U ` F ) = ( V ` F ) ) /\ ( F e. T /\ F =/= ( _I |` B ) ) ) -> U = V )

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
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    cF
    cU
    cfv
    cF
    cV
    cfv
    wceq
    #
    w3a
    #
    cF
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    wa
    #
    w3a
    #
    @0
    @1
    @3
    @4
    vh
    cv
    #
    @8
    wne
    #
    @12
    cU
    cfv
    @12
    cV
    cfv
    wceq
    #
    wi
    #
    vh
    cT
    wral
    cU
    cV
    wceq
    @0
    @1
    @6
    @10
    simp1l
    @0
    @1
    @6
    @10
    simp1r
    @2
    @3
    @4
    @5
    @10
    simp21
    @2
    @3
    @4
    @5
    @10
    simp22
    @11
    @15
    vh
    cT
    @11
    @12
    cT
    wcel
    #
    @13
    @14
    @11
    @16
    @13
    w3a
    #
    @2
    @6
    @7
    @9
    @16
    w3a
    @13
    @14
    @2
    @6
    @10
    @16
    @13
    simp11
    @2
    @6
    @10
    @16
    @13
    simp12
    @17
    @7
    @9
    @16
    @7
    @9
    @2
    @6
    @16
    @13
    simp13l
    @7
    @9
    @2
    @6
    @16
    @13
    simp13r
    @11
    @16
    @13
    simp2
    3jca
    @11
    @16
    @13
    simp3
    cB
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cT
    cU
    vh
    cE
    cF
    cH
    cK
    cV
    cW
    tendocan.b
    tendocan.h
    tendocan.t
    @18
    eqid
    tendocan.e
    cdlemj3
    syl31anc
    3exp
    ralrimiv
    cB
    cT
    cU
    vh
    cE
    cH
    cK
    cV
    cW
    tendocan.b
    tendocan.h
    tendocan.t
    tendocan.e
    tendoeq2
    syl221anc
end
