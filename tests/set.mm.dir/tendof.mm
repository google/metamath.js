include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "ctrl.mm"
include "cple.mm"
include "wbr.mm"
include "w3a.mm"
include "eqid.mm"
include "istendo.mm"
include "simp1.mm"
include "syl6bi.mm"
include "imp.mm"

theorem tendof
  let cS: class S
  let cT: class T
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ S e. E ) -> S : T --> T )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
    #
    cT
    cT
    cS
    wf
    #
    @0
    @1
    @2
    vf
    cv
    #
    vg
    cv
    #
    ccom
    cS
    cfv
    @3
    cS
    cfv
    #
    @4
    cS
    cfv
    ccom
    wceq
    vg
    cT
    wral
    vf
    cT
    wral
    #
    @5
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    @3
    @7
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
    @2
    @7
    cS
    cT
    vf
    vg
    cE
    cH
    cK
    @8
    cV
    cW
    @8
    eqid
    tendof.h
    tendof.t
    @7
    eqid
    tendof.e
    istendo
    @2
    @6
    @9
    simp1
    syl6bi
    imp
end
