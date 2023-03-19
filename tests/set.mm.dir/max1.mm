include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "rexr.mm"
include "xrmax1.mm"
include "syl2an.mm"

theorem max1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> A <_ if ( A <_ B , B , A ) )

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
    xrmax1
    syl2an
end
