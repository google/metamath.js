include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wf.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "tendof.mm"
include "syl2anc.mm"
include "simp3.mm"
include "fvco3.mm"

theorem tendocoval
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let cS: class S
  let cG: class G
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. X /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ F e. T ) -> ( ( U o. V ) ` F ) = ( U ` ( V ` F ) ) )

  proof
    cK
    cX
    wcel
    cW
    cH
    wcel
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
    w3a
    #
    cT
    cT
    cV
    wf
    #
    @4
    cF
    cU
    cV
    ccom
    cfv
    cF
    cV
    cfv
    cU
    cfv
    wceq
    @5
    @0
    @2
    @6
    @0
    @3
    @4
    simp1
    @0
    @1
    @2
    @4
    simp2r
    cV
    cT
    cE
    cH
    cK
    cX
    cW
    tendof.h
    tendof.t
    tendof.e
    tendof
    syl2anc
    @0
    @3
    @4
    simp3
    cT
    cT
    cF
    cU
    cV
    fvco3
    syl2anc
end
