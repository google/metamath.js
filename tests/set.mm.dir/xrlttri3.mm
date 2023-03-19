include "cxr.mm"
include "clt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "xrltso.mm"
include "sotrieq2.mm"
include "mpan.mm"

theorem xrlttri3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A = B <-> ( -. A < B /\ -. B < A ) ) )

  proof
    cxr
    clt
    wor
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    cA
    cB
    wceq
    cA
    cB
    clt
    wbr
    wn
    cB
    cA
    clt
    wbr
    wn
    wa
    wb
    xrltso
    cxr
    cA
    cB
    clt
    sotrieq2
    mpan
end
