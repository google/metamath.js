include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "rexr.mm"
include "xrmax2.mm"
include "syl2an.mm"

theorem max2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> B <_ if ( A <_ B , B , A ) )

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
    cB
    cA
    cB
    cle
    wbr
    cB
    cA
    cif
    cle
    wbr
    cB
    cr
    wcel
    cA
    rexr
    cB
    rexr
    cA
    cB
    xrmax2
    syl2an
end
