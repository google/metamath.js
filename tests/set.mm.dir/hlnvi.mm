include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "hlnv.mm"
include "ax-mp.mm"

theorem hlnvi
  let cU: class U
  assume hlnvi.1: |- U e. CHilOLD


  assert |- U e. NrmCVec

  proof
    cU
    chlo
    wcel
    cU
    cnv
    wcel
    hlnvi.1
    cU
    hlnv
    ax-mp
end
