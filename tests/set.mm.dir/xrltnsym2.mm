include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "xrltnsym.mm"
include "imnan.mm"
include "sylib.mm"

theorem xrltnsym2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> -. ( A < B /\ B < A ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    wn
    wi
    @0
    @1
    wa
    wn
    cA
    cB
    xrltnsym
    @0
    @1
    imnan
    sylib
end
