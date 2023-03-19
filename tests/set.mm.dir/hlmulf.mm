include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "hlnv.mm"
include "nvsf.mm"
include "syl.mm"

theorem hlmulf
  let cS: class S
  let cU: class U
  let cX: class X
  assume hlmulf.1: |- X = ( BaseSet ` U )
  assume hlmulf.4: |- S = ( .sOLD ` U )


  assert |- ( U e. CHilOLD -> S : ( CC X. X ) --> X )

  proof
    cU
    chlo
    wcel
    cU
    cnv
    wcel
    cc
    cX
    cxp
    cX
    cS
    wf
    cU
    hlnv
    cS
    cU
    cX
    hlmulf.1
    hlmulf.4
    nvsf
    syl
end
