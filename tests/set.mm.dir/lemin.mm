include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wa.mm"
include "wb.mm"
include "rexr.mm"
include "xrlemin.mm"
include "syl3an.mm"

theorem lemin
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <_ if ( B <_ C , B , C ) <-> ( A <_ B /\ A <_ C ) ) )

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
    cC
    cle
    wbr
    cB
    cC
    cif
    cle
    wbr
    cA
    cB
    cle
    wbr
    cA
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
    xrlemin
    syl3an
end
