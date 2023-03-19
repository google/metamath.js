include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "rexr.mm"
include "xrmin2.mm"
include "syl2an.mm"

theorem min2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> if ( A <_ B , A , B ) <_ B )

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
    cB
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
    xrmin2
    syl2an
end
