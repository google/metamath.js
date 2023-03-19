include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "elfzolt2.mm"
include "elfzoel2.mm"
include "zred.mm"
include "ltnrd.mm"
include "pm2.65i.mm"

theorem fzonel
  let cA: class A
  let cB: class B


  assert |- -. B e. ( A ..^ B )

  proof
    cB
    cA
    cB
    cfzo
    co
    wcel
    #
    cB
    cB
    clt
    wbr
    cB
    cA
    cB
    elfzolt2
    @0
    cB
    @0
    cB
    cB
    cA
    cB
    elfzoel2
    zred
    ltnrd
    pm2.65i
end
