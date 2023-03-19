include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "wa.mm"
include "xrmax1.mm"
include "3adant3.mm"
include "wi.mm"
include "ifcl.mm"
include "ancoms.mm"
include "xrlelttr.mm"
include "syld3an2.mm"
include "mpand.mm"
include "xrmax2.mm"
include "simp2.mm"
include "simp3.mm"
include "syl3anc.mm"
include "jcad.mm"
include "breq1.mm"
include "ifboth.mm"
include "impbid1.mm"

theorem xrmaxlt
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( if ( A <_ B , B , A ) < C <-> ( A < C /\ B < C ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cif
    #
    cC
    clt
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    wa
    @3
    @6
    @7
    @8
    @3
    cA
    @5
    cle
    wbr
    #
    @6
    @7
    @0
    @1
    @9
    @2
    cA
    cB
    xrmax1
    3adant3
    @0
    @5
    cxr
    wcel
    #
    @1
    @2
    @9
    @6
    wa
    @7
    wi
    @0
    @1
    @10
    @2
    @1
    @0
    @10
    @4
    cB
    cA
    cxr
    ifcl
    ancoms
    3adant3
    #
    cA
    @5
    cC
    xrlelttr
    syld3an2
    mpand
    @3
    cB
    @5
    cle
    wbr
    #
    @6
    @8
    @0
    @1
    @12
    @2
    cA
    cB
    xrmax2
    3adant3
    @3
    @1
    @10
    @2
    @12
    @6
    wa
    @8
    wi
    @0
    @1
    @2
    simp2
    @11
    @0
    @1
    @2
    simp3
    cB
    @5
    cC
    xrlelttr
    syl3anc
    mpand
    jcad
    @8
    @7
    @6
    @4
    @8
    @7
    @6
    cB
    cA
    cB
    @5
    cC
    clt
    breq1
    cA
    @5
    cC
    clt
    breq1
    ifboth
    ancoms
    impbid1
end
