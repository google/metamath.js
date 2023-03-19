include "cr.mm"
include "clt.mm"
include "wor.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "ltso.mm"
include "sonr.mm"
include "mpan.mm"

theorem ltnr
  let cA: class A


  assert |- ( A e. RR -> -. A < A )

  proof
    cr
    clt
    wor
    cA
    cr
    wcel
    cA
    cA
    clt
    wbr
    wn
    ltso
    cr
    cA
    clt
    sonr
    mpan
end
