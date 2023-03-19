include "hlnvi.mm"
include "hilhhi.mm"
include "hhcmpl.mm"

theorem hilcompl
  let vx: setvar x
  let cD: class D
  let cU: class U
  let cF: class F
  let cJ: class J
  assume hilcompl.1: |- ~H = ( BaseSet ` U )
  assume hilcompl.2: |- +h = ( +v ` U )
  assume hilcompl.3: |- .h = ( .sOLD ` U )
  assume hilcompl.4: |- .ih = ( .iOLD ` U )
  assume hilcompl.5: |- D = ( IndMet ` U )
  assume hilcompl.6: |- J = ( MetOpen ` D )
  assume hilcompl.7: |- U e. CHilOLD
  assume hilcompl.8: |- ( F e. ( Cau ` D ) -> E. x e. ~H F ( ~~>t ` J ) x )

  disjoint F x
  assert |- ( F e. Cauchy -> E. x e. ~H F ~~>v x )

  proof
    vx
    cD
    cU
    cF
    cJ
    cU
    hilcompl.1
    hilcompl.2
    hilcompl.3
    hilcompl.4
    cU
    hilcompl.7
    hlnvi
    hilhhi
    hilcompl.5
    hilcompl.6
    hilcompl.8
    hhcmpl
end
