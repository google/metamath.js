include "ccph.mm"
include "wcel.mm"
include "cnlm.mm"
include "clvec.mm"
include "cnvc.mm"
include "cphnlm.mm"
include "cphlvec.mm"
include "isnvc.mm"
include "sylanbrc.mm"

theorem cphnvc
  let cW: class W


  assert |- ( W e. CPreHil -> W e. NrmVec )

  proof
    cW
    ccph
    wcel
    cW
    cnlm
    wcel
    cW
    clvec
    wcel
    cW
    cnvc
    wcel
    cW
    cphnlm
    cW
    cphlvec
    cW
    isnvc
    sylanbrc
end
