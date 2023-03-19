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
include "xrmaxlt.mm"
include "syl3an.mm"

theorem maxlt
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( if ( A <_ B , B , A ) < C <-> ( A < C /\ B < C ) ) )

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
    clt
    wbr
    cA
    cC
    clt
    wbr
    cB
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
    xrmaxlt
    syl3an
end
