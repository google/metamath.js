include "cuni.mm"
include "cpw.mm"
include "wcel.mm"
include "wn.mm"
include "cvv.mm"
include "pwexr.mm"
include "pwuninel2.mm"
include "syl.mm"
include "id.mm"
include "pm2.61i.mm"

theorem pwuninel
  let cA: class A


  assert |- -. ~P U. A e. A

  proof
    cA
    cuni
    #
    cpw
    cA
    wcel
    #
    @1
    wn
    #
    @1
    @0
    cvv
    wcel
    @2
    @0
    cA
    pwexr
    cA
    cvv
    pwuninel2
    syl
    @2
    id
    pm2.61i
end
