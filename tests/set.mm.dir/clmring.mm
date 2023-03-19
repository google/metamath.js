include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "crg.mm"
include "clmlmod.mm"
include "lmodring.mm"
include "syl.mm"

theorem clmring
  let cF: class F
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )


  assert |- ( W e. CMod -> F e. Ring )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cF
    crg
    wcel
    cW
    clmlmod
    cF
    cW
    clm0.f
    lmodring
    syl
end
