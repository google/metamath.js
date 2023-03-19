include "con0.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csuc.mm"
include "wceq.mm"
include "onprc.mm"
include "sucprc.mm"
include "ax-mp.mm"

theorem sucon



  assert |- suc On = On

  proof
    con0
    cvv
    wcel
    wn
    con0
    csuc
    con0
    wceq
    onprc
    con0
    sucprc
    ax-mp
end
