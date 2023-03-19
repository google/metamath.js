include "cvv.mm"
include "wcel.mm"
include "csdm.mm"
include "wbr.mm"
include "wn.mm"
include "cen.mm"
include "sdomnen.mm"
include "enrefg.mm"
include "nsyl3.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "con3i.mm"
include "pm2.61i.mm"

theorem sdomirr
  let cA: class A


  assert |- -. A ~< A

  proof
    cA
    cvv
    wcel
    #
    cA
    cA
    csdm
    wbr
    #
    wn
    @1
    cA
    cA
    cen
    wbr
    @0
    cA
    cA
    sdomnen
    cA
    cvv
    enrefg
    nsyl3
    @1
    @0
    cA
    cA
    csdm
    relsdom
    brrelexi
    con3i
    pm2.61i
end
