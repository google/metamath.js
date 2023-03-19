include "cbits.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "bitsval.mm"
include "simp2bi.mm"
include "ssriv.mm"

theorem bitsss
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let vm: setvar m


  assert |- ( bits ` N ) C_ NN0

  proof
    vm
    cN
    cbits
    cfv
    #
    cn0
    vm
    cv
    #
    @0
    wcel
    cN
    cz
    wcel
    @1
    cn0
    wcel
    c2
    cN
    c2
    @1
    cexp
    co
    cdiv
    co
    cfl
    cfv
    cdvds
    wbr
    wn
    @1
    cN
    bitsval
    simp2bi
    ssriv
end
