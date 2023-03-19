include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wf.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "tendof.mm"
include "3ad2antr2.mm"
include "simpr3.mm"
include "fvco3.mm"
include "syl2anc.mm"

theorem tendospass
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume tendosp.h: |- H = ( LHyp ` K )
  assume tendosp.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendosp.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. X /\ W e. H ) /\ ( U e. E /\ V e. E /\ F e. T ) ) -> ( ( U o. V ) ` F ) = ( U ` ( V ` F ) ) )

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
    cF
    cT
    wcel
    #
    w3a
    wa
    cT
    cT
    cV
    wf
    #
    @3
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
    @0
    @1
    @2
    @4
    @3
    cV
    cT
    cE
    cH
    cK
    cX
    cW
    tendosp.h
    tendosp.t
    tendosp.e
    tendof
    3ad2antr2
    @0
    @1
    @2
    @3
    simpr3
    cT
    cT
    cF
    cU
    cV
    fvco3
    syl2anc
end
