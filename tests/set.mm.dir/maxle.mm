include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wa.mm"
include "wb.mm"
include "rexr.mm"
include "xrmaxle.mm"
include "syl3an.mm"

theorem maxle
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( if ( A <_ B , B , A ) <_ C <-> ( A <_ C /\ B <_ C ) ) )

  proof
    cA
    cr
    wcel
    cA
    cxr
    wcel
    cB
    cr
    wcel
    cB
    cxr
    wcel
    cC
    cr
    wcel
    cC
    cxr
    wcel
    cA
    cB
    cle
    wbr
    cB
    cA
    cif
    cC
    cle
    wbr
    cA
    cC
    cle
    wbr
    cB
    cC
    cle
    wbr
    wa
    wb
    cA
    rexr
    cB
    rexr
    cC
    rexr
    cA
    cB
    cC
    xrmaxle
    syl3an
end
