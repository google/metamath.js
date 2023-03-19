include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cxp.mm"
include "cc.mm"
include "wf.mm"
include "hlnv.mm"
include "ipf.mm"
include "syl.mm"

theorem hlipf
  let cP: class P
  let cU: class U
  let cX: class X
  assume hlipf.1: |- X = ( BaseSet ` U )
  assume hlipf.7: |- P = ( .iOLD ` U )


  assert |- ( U e. CHilOLD -> P : ( X X. X ) --> CC )

  proof
    cU
    chlo
    wcel
    cU
    cnv
    wcel
    cX
    cX
    cxp
    cc
    cP
    wf
    cU
    hlnv
    cP
    cU
    cX
    hlipf.1
    hlipf.7
    ipf
    syl
end
