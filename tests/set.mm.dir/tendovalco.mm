include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wf.mm"
include "cv.mm"
include "wral.mm"
include "ctrl.mm"
include "cple.mm"
include "wbr.mm"
include "eqid.mm"
include "istendo.mm"
include "coeq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "coeq1d.mm"
include "eqeq12d.mm"
include "coeq2.mm"
include "coeq2d.mm"
include "rspc2v.mm"
include "com12.mm"
include "3ad2ant2.mm"
include "syl6bi.mm"
include "3impia.mm"
include "imp.mm"

theorem tendovalco
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let cU: class U
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H /\ S e. E ) /\ ( F e. T /\ G e. T ) ) -> ( S ` ( F o. G ) ) = ( ( S ` F ) o. ( S ` G ) ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    #
    cS
    cE
    wcel
    #
    w3a
    cF
    cT
    wcel
    cG
    cT
    wcel
    wa
    #
    cF
    cG
    ccom
    #
    cS
    cfv
    #
    cF
    cS
    cfv
    #
    cG
    cS
    cfv
    #
    ccom
    #
    wceq
    #
    @0
    @1
    @2
    @3
    @9
    wi
    #
    @0
    @1
    wa
    @2
    cT
    cT
    cS
    wf
    #
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    cS
    cfv
    #
    @12
    cS
    cfv
    #
    @13
    cS
    cfv
    #
    ccom
    #
    wceq
    #
    vg
    cT
    wral
    vf
    cT
    wral
    #
    @16
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    @12
    @21
    cfv
    cK
    cple
    cfv
    #
    wbr
    vf
    cT
    wral
    #
    w3a
    @10
    @21
    cS
    cT
    vf
    vg
    cE
    cH
    cK
    @22
    cV
    cW
    @22
    eqid
    tendof.h
    tendof.t
    @21
    eqid
    tendof.e
    istendo
    @20
    @11
    @10
    @23
    @3
    @20
    @9
    @19
    @9
    cF
    @13
    ccom
    #
    cS
    cfv
    #
    @6
    @17
    ccom
    #
    wceq
    vf
    vg
    cF
    cG
    cT
    cT
    @12
    cF
    wceq
    #
    @15
    @25
    @18
    @26
    @27
    @14
    @24
    cS
    @12
    cF
    @13
    coeq1
    fveq2d
    @27
    @16
    @6
    @17
    @12
    cF
    cS
    fveq2
    coeq1d
    eqeq12d
    @13
    cG
    wceq
    #
    @25
    @5
    @26
    @8
    @28
    @24
    @4
    cS
    @13
    cG
    cF
    coeq2
    fveq2d
    @28
    @17
    @7
    @6
    @13
    cG
    cS
    fveq2
    coeq2d
    eqeq12d
    rspc2v
    com12
    3ad2ant2
    syl6bi
    3impia
    imp
end
