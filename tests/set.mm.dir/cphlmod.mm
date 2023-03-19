include "ccph.mm"
include "wcel.mm"
include "cnlm.mm"
include "clmod.mm"
include "cphnlm.mm"
include "nlmlmod.mm"
include "syl.mm"

theorem cphlmod
  let cW: class W


  assert |- ( W e. CPreHil -> W e. LMod )

  proof
    cW
    ccph
    wcel
    cW
    cnlm
    wcel
    cW
    clmod
    wcel
    cW
    cphnlm
    cW
    nlmlmod
    syl
end
