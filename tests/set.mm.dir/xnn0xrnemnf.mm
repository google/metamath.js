include "cxnn0.mm"
include "wcel.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "xnn0xr.mm"
include "xnn0nemnf.mm"
include "jca.mm"

theorem xnn0xrnemnf
  let cA: class A


  assert |- ( A e. NN0* -> ( A e. RR* /\ A =/= -oo ) )

  proof
    cA
    cxnn0
    wcel
    cA
    cxr
    wcel
    cA
    cmnf
    wne
    cA
    xnn0xr
    cA
    xnn0nemnf
    jca
end
