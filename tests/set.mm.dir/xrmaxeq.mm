include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "xrletri3.mm"
include "ancoms.mm"
include "biimpar.mm"
include "anassrs.mm"
include "ifeq1da.mm"
include "3impa.mm"
include "ifid.mm"
include "syl6eq.mm"

theorem xrmaxeq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ B <_ A ) -> if ( A <_ B , B , A ) = A )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cB
    cA
    cle
    wbr
    #
    w3a
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cif
    #
    @3
    cA
    cA
    cif
    #
    cA
    @0
    @1
    @2
    @4
    @5
    wceq
    @0
    @1
    wa
    #
    @2
    wa
    @3
    cB
    cA
    cA
    @6
    @2
    @3
    cB
    cA
    wceq
    #
    @6
    @7
    @2
    @3
    wa
    #
    @1
    @0
    @7
    @8
    wb
    cB
    cA
    xrletri3
    ancoms
    biimpar
    anassrs
    ifeq1da
    3impa
    @3
    cA
    ifid
    syl6eq
end
