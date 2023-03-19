include "cn.mm"
include "wcel.mm"
include "cphi.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "phicl2.mm"
include "elfznn.mm"
include "syl.mm"

theorem phicl
  let cN: class N
  let vx: setvar x


  assert |- ( N e. NN -> ( phi ` N ) e. NN )

  proof
    cN
    cn
    wcel
    cN
    cphi
    cfv
    #
    c1
    cN
    cfz
    co
    wcel
    @0
    cn
    wcel
    cN
    phicl2
    @0
    cN
    elfznn
    syl
end
