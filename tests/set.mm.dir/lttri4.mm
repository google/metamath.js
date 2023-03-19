include "cr.mm"
include "clt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "ltso.mm"
include "solin.mm"
include "mpan.mm"

theorem lttri4
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B \/ A = B \/ B < A ) )

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
    clt
    wbr
    cA
    cB
    wceq
    cB
    cA
    clt
    wbr
    w3o
    ltso
    cr
    cA
    cB
    clt
    solin
    mpan
end
