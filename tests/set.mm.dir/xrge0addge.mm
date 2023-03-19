include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxad.mm"
include "elxrge0.mm"
include "biimpi.mm"
include "xraddge02.mm"
include "impr.mm"
include "sylan2.mm"

theorem xrge0addge
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. ( 0 [,] +oo ) ) -> A <_ ( A +e B ) )

  proof
    cB
    cc0
    cpnf
    cicc
    co
    wcel
    #
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cA
    cA
    cB
    cxad
    co
    cle
    wbr
    #
    @0
    @4
    cB
    elxrge0
    biimpi
    @1
    @2
    @3
    @5
    cA
    cB
    xraddge02
    impr
    sylan2
end
