include "com.mm"
include "wlim.mm"
include "wcel.mm"
include "csuc.mm"
include "wb.mm"
include "limom.mm"
include "limsuc.mm"
include "ax-mp.mm"

theorem peano2b
  let cA: class A


  assert |- ( A e. _om <-> suc A e. _om )

  proof
    com
    wlim
    cA
    com
    wcel
    cA
    csuc
    com
    wcel
    wb
    limom
    com
    cA
    limsuc
    ax-mp
end
