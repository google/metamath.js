include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "wa.mm"
include "wb.mm"
include "rexr.mm"
include "xrltmin.mm"
include "syl3an.mm"

theorem ltmin
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A < if ( B <_ C , B , C ) <-> ( A < B /\ A < C ) ) )

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
    clt
    wbr
    cA
    cB
    clt
    wbr
    cA
    cC
    clt
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
    xrltmin
    syl3an
end
