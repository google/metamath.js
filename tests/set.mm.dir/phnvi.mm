include "ccphlo.mm"
include "wcel.mm"
include "cnv.mm"
include "phnv.mm"
include "ax-mp.mm"

theorem phnvi
  let cU: class U
  assume phnvi.1: |- U e. CPreHilOLD


  assert |- U e. NrmCVec

  proof
    cU
    ccphlo
    wcel
    cU
    cnv
    wcel
    phnvi.1
    cU
    phnv
    ax-mp
end
