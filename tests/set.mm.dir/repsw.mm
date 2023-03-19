include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "creps.mm"
include "wf.mm"
include "cword.mm"
include "repsf.mm"
include "iswrdi.mm"
include "syl.mm"

theorem repsw
  let cS: class S
  let cN: class N
  let cV: class V


  assert |- ( ( S e. V /\ N e. NN0 ) -> ( S repeatS N ) e. Word V )

  proof
    cS
    cV
    wcel
    cN
    cn0
    wcel
    wa
    cc0
    cN
    cfzo
    co
    cV
    cS
    cN
    creps
    co
    #
    wf
    @0
    cV
    cword
    wcel
    cS
    cN
    cV
    repsf
    cV
    cN
    @0
    iswrdi
    syl
end
