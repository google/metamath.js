include "c0.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cvv.mm"
include "wcel.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "0domg.mm"
include "syl.mm"
include "domnsym.mm"
include "con2i.mm"
include "pm2.65i.mm"

theorem sdom0
  let cA: class A


  assert |- -. A ~< (/)

  proof
    cA
    c0
    csdm
    wbr
    #
    c0
    cA
    cdom
    wbr
    #
    @0
    cA
    cvv
    wcel
    @1
    cA
    c0
    csdm
    relsdom
    brrelexi
    cA
    cvv
    0domg
    syl
    @1
    @0
    c0
    cA
    domnsym
    con2i
    pm2.65i
end
