include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cif.mm"
include "ifid.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "xrletri3.mm"
include "ancoms.mm"
include "biimpar.mm"
include "anassrs.mm"
include "ifeq1da.mm"
include "3impa.mm"
include "syl5reqr.mm"

theorem xrmineq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ B <_ A ) -> if ( A <_ B , A , B ) = B )

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
    cB
    cA
    cB
    cle
    wbr
    #
    cB
    cB
    cif
    #
    @3
    cA
    cB
    cif
    #
    @3
    cB
    ifid
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
    cB
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
    syl5reqr
end
