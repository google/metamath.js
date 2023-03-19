include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "tendovalco.mm"
include "syl32anc.mm"

theorem tendospdi1
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume tendosp.h: |- H = ( LHyp ` K )
  assume tendosp.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendosp.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( U e. E /\ F e. T /\ G e. T ) ) -> ( U ` ( F o. G ) ) = ( ( U ` F ) o. ( U ` G ) ) )

  proof
    cK
    cV
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
    wa
    @0
    @1
    @3
    @4
    @5
    cF
    cG
    ccom
    cU
    cfv
    cF
    cU
    cfv
    cG
    cU
    cfv
    ccom
    wceq
    @0
    @1
    @6
    simpll
    @0
    @1
    @6
    simplr
    @2
    @3
    @4
    @5
    simpr1
    @2
    @3
    @4
    @5
    simpr2
    @2
    @3
    @4
    @5
    simpr3
    cU
    cT
    cE
    cF
    cG
    cH
    cK
    cV
    cW
    tendosp.h
    tendosp.t
    tendosp.e
    tendovalco
    syl32anc
end
