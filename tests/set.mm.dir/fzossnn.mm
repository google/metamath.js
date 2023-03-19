include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cfz.mm"
include "cn.mm"
include "fzossfz.mm"
include "cv.mm"
include "elfznn.mm"
include "ssriv.mm"
include "sstri.mm"

theorem fzossnn
  let cN: class N
  let vk: setvar k


  assert |- ( 1 ..^ N ) C_ NN

  proof
    c1
    cN
    cfzo
    co
    c1
    cN
    cfz
    co
    #
    cn
    c1
    cN
    fzossfz
    vk
    @0
    cn
    vk
    cv
    cN
    elfznn
    ssriv
    sstri
end
