include "cn.mm"
include "wcel.mm"
include "cphi.mm"
include "cfv.mm"
include "phicl.mm"
include "syl.mm"

theorem phicld
  let wph: wff ph
  let cN: class N
  let vx: setvar x
  assume phicld.1: |- ( ph -> N e. NN )


  assert |- ( ph -> ( phi ` N ) e. NN )

  proof
    wph
    cN
    cn
    wcel
    cN
    cphi
    cfv
    cn
    wcel
    phicld.1
    cN
    phicl
    syl
end
