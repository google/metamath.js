include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "id.mm"
include "peano2cnm.mm"
include "mulcld.mm"

theorem kcnktkm1cn
  let cK: class K


  assert |- ( K e. CC -> ( K x. ( K - 1 ) ) e. CC )

  proof
    cK
    cc
    wcel
    #
    cK
    cK
    c1
    cmin
    co
    @0
    id
    cK
    peano2cnm
    mulcld
end
