include "cr.mm"
include "clt.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "ltso.mm"
include "so2nr.mm"
include "mpan.mm"

theorem ltnsym2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> -. ( A < B /\ B < A ) )

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
    cB
    cA
    clt
    wbr
    wa
    wn
    ltso
    cr
    cA
    cB
    clt
    so2nr
    mpan
end
