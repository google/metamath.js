include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cvc.mm"
include "hlnv.mm"
include "nvvc.mm"
include "syl.mm"

theorem hlvc
  let cU: class U
  let cW: class W
  assume hlvc.1: |- W = ( 1st ` U )


  assert |- ( U e. CHilOLD -> W e. CVecOLD )

  proof
    cU
    chlo
    wcel
    cU
    cnv
    wcel
    cW
    cvc
    wcel
    cU
    hlnv
    cU
    cW
    hlvc.1
    nvvc
    syl
end
