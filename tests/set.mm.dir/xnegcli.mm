include "cxr.mm"
include "wcel.mm"
include "cxne.mm"
include "xnegcl.mm"
include "ax-mp.mm"

theorem xnegcli
  let cA: class A
  assume xnegcli.1: |- A e. RR*


  assert |- -e A e. RR*

  proof
    cA
    cxr
    wcel
    cA
    cxne
    cxr
    wcel
    xnegcli.1
    cA
    xnegcl
    ax-mp
end
