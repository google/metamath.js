include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "rexr.mm"
include "xrmin1.mm"
include "syl2an.mm"

theorem min1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> if ( A <_ B , A , B ) <_ A )

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
    cA
    cB
    cif
    cA
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
    xrmin1
    syl2an
end
