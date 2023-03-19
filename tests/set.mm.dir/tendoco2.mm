include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp3l.mm"
include "simp3r.mm"
include "tendovalco.mm"
include "syl32anc.mm"
include "simp2r.mm"
include "coeq12d.mm"
include "simp1.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "ltrnco4.mm"
include "eqtrd.mm"

theorem tendoco2
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let cS: class S
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ ( F e. T /\ G e. T ) ) -> ( ( U ` ( F o. G ) ) o. ( V ` ( F o. G ) ) ) = ( ( ( U ` F ) o. ( V ` F ) ) o. ( ( U ` G ) o. ( V ` G ) ) ) )

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
    w3a
    #
    cF
    cG
    ccom
    #
    cU
    cfv
    #
    @10
    cV
    cfv
    #
    ccom
    cF
    cU
    cfv
    #
    cG
    cU
    cfv
    #
    ccom
    #
    cF
    cV
    cfv
    #
    cG
    cV
    cfv
    #
    ccom
    #
    ccom
    #
    @13
    @16
    ccom
    @14
    @17
    ccom
    ccom
    #
    @9
    @11
    @15
    @12
    @18
    @9
    @0
    @1
    @3
    @6
    @7
    @11
    @15
    wceq
    @0
    @1
    @5
    @8
    simp1l
    #
    @0
    @1
    @5
    @8
    simp1r
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @5
    @6
    @7
    simp3l
    #
    @2
    @5
    @6
    @7
    simp3r
    #
    cU
    cT
    cE
    cF
    cG
    cH
    cK
    chlt
    cW
    tendof.h
    tendof.t
    tendof.e
    tendovalco
    syl32anc
    @9
    @0
    @1
    @4
    @6
    @7
    @12
    @18
    wceq
    @21
    @22
    @2
    @3
    @4
    @8
    simp2r
    #
    @24
    @25
    cV
    cT
    cE
    cF
    cG
    cH
    cK
    chlt
    cW
    tendof.h
    tendof.t
    tendof.e
    tendovalco
    syl32anc
    coeq12d
    @9
    @2
    @14
    cT
    wcel
    #
    @16
    cT
    wcel
    #
    @19
    @20
    wceq
    @2
    @5
    @8
    simp1
    #
    @9
    @2
    @3
    @7
    @27
    @29
    @23
    @25
    cU
    cT
    cE
    cG
    cH
    cK
    chlt
    cW
    tendof.h
    tendof.t
    tendof.e
    tendocl
    syl3anc
    @9
    @2
    @4
    @6
    @28
    @29
    @26
    @24
    cV
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendof.h
    tendof.t
    tendof.e
    tendocl
    syl3anc
    @13
    cT
    @14
    @16
    @17
    cH
    cK
    cW
    tendof.h
    tendof.t
    ltrnco4
    syl3anc
    eqtrd
end
