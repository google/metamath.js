include "cn0.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "cn.mm"
include "faccl.mm"
include "syl.mm"

theorem faccld
  let wph: wff ph
  let cN: class N
  assume faccld.1: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( ! ` N ) e. NN )

  proof
    wph
    cN
    cn0
    wcel
    cN
    cfa
    cfv
    cn
    wcel
    faccld.1
    cN
    faccl
    syl
end
