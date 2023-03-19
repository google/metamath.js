include "chlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "cnv.mm"
include "hlobn.mm"
include "bnnv.mm"
include "syl.mm"

theorem hlnv
  let cU: class U


  assert |- ( U e. CHilOLD -> U e. NrmCVec )

  proof
    cU
    chlo
    wcel
    cU
    ccbn
    wcel
    cU
    cnv
    wcel
    cU
    hlobn
    cU
    bnnv
    syl
end
