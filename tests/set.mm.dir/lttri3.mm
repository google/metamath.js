include "cr.mm"
include "clt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "ltso.mm"
include "sotrieq2.mm"
include "mpan.mm"

theorem lttri3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A = B <-> ( -. A < B /\ -. B < A ) ) )

  proof
    cr
    clt
    wor
    cA
    cr
    wcel
    cB
    cr
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
    ltso
    cr
    cA
    cB
    clt
    sotrieq2
    mpan
end
