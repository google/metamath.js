include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "simp3.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "simp1.mm"
include "simp2l.mm"
include "tendof.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "simp2r.mm"
include "eqfnfv.mm"
include "mpbird.mm"

theorem tendoeq1
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vg: setvar g
  let cS: class S
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint K f
  disjoint T f
  disjoint W f
  disjoint U f
  disjoint V f
  disjoint f g
  disjoint K g
  disjoint S f
  disjoint S g
  disjoint T g
  disjoint W g
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ A. f e. T ( U ` f ) = ( V ` f ) ) -> U = V )

  proof
    cK
    chlt
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
    vf
    cv
    #
    cU
    cfv
    @4
    cV
    cfv
    wceq
    vf
    cT
    wral
    #
    w3a
    #
    cU
    cV
    wceq
    #
    @5
    @0
    @3
    @5
    simp3
    @6
    cU
    cT
    wfn
    #
    cV
    cT
    wfn
    #
    @7
    @5
    wb
    @6
    cT
    cT
    cU
    wf
    #
    @8
    @6
    @0
    @1
    @10
    @0
    @3
    @5
    simp1
    #
    @0
    @1
    @2
    @5
    simp2l
    cU
    cT
    cE
    cH
    cK
    chlt
    cW
    tendof.h
    tendof.t
    tendof.e
    tendof
    syl2anc
    cT
    cT
    cU
    ffn
    syl
    @6
    cT
    cT
    cV
    wf
    #
    @9
    @6
    @0
    @2
    @12
    @11
    @0
    @1
    @2
    @5
    simp2r
    cV
    cT
    cE
    cH
    cK
    chlt
    cW
    tendof.h
    tendof.t
    tendof.e
    tendof
    syl2anc
    cT
    cT
    cV
    ffn
    syl
    vf
    cT
    cU
    cV
    eqfnfv
    syl2anc
    mpbird
end
