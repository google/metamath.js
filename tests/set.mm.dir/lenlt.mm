include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wb.mm"
include "rexr.mm"
include "xrlenlt.mm"
include "syl2an.mm"

theorem lenlt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B <-> -. B < A ) )

  proof
    cA
    cr
    wcel
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    cB
    cA
    clt
    wbr
    wn
    wb
    cB
    cr
    wcel
    cA
    rexr
    cB
    rexr
    cA
    cB
    xrlenlt
    syl2an
end
