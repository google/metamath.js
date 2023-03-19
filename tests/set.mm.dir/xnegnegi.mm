include "cxr.mm"
include "wcel.mm"
include "cxne.mm"
include "wceq.mm"
include "xnegneg.mm"
include "ax-mp.mm"

theorem xnegnegi
  let cA: class A
  assume xnegnegi.1: |- A e. RR*


  assert |- -e -e A = A

  proof
    cA
    cxr
    wcel
    cA
    cxne
    cxne
    cA
    wceq
    xnegnegi.1
    cA
    xnegneg
    ax-mp
end
