include "ccph.mm"
include "wcel.mm"
include "cphl.mm"
include "clvec.mm"
include "cphphl.mm"
include "phllvec.mm"
include "syl.mm"

theorem cphlvec
  let cW: class W


  assert |- ( W e. CPreHil -> W e. LVec )

  proof
    cW
    ccph
    wcel
    cW
    cphl
    wcel
    cW
    clvec
    wcel
    cW
    cphphl
    cW
    phllvec
    syl
end
