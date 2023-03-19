include "tendocl.mm"

theorem tendospcl
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume tendosp.h: |- H = ( LHyp ` K )
  assume tendosp.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendosp.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ U e. E /\ F e. T ) -> ( U ` F ) e. T )

  proof
    cU
    cT
    cE
    cF
    cH
    cK
    cV
    cW
    tendosp.h
    tendosp.t
    tendosp.e
    tendocl
end
