include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "wa.mm"
include "xrmin1.mm"
include "3adant1.mm"
include "wi.mm"
include "simp1.mm"
include "ifcl.mm"
include "simp2.mm"
include "xrltletr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "xrmin2.mm"
include "syld3an2.mm"
include "jcad.mm"
include "breq2.mm"
include "ifboth.mm"
include "impbid1.mm"

theorem xrltmin
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( A < if ( B <_ C , B , C ) <-> ( A < B /\ A < C ) ) )

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
    cC
    cle
    wbr
    #
    cB
    cC
    cif
    #
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    cA
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
    @6
    @5
    cB
    cle
    wbr
    #
    @7
    @1
    @2
    @9
    @0
    cB
    cC
    xrmin1
    3adant1
    @3
    @0
    @5
    cxr
    wcel
    #
    @1
    @6
    @9
    wa
    @7
    wi
    @0
    @1
    @2
    simp1
    @1
    @2
    @10
    @0
    @4
    cB
    cC
    cxr
    ifcl
    3adant1
    #
    @0
    @1
    @2
    simp2
    cA
    @5
    cB
    xrltletr
    syl3anc
    mpan2d
    @3
    @6
    @5
    cC
    cle
    wbr
    #
    @8
    @1
    @2
    @12
    @0
    cB
    cC
    xrmin2
    3adant1
    @0
    @10
    @1
    @2
    @6
    @12
    wa
    @8
    wi
    @11
    cA
    @5
    cC
    xrltletr
    syld3an2
    mpan2d
    jcad
    @4
    @7
    @8
    @6
    cB
    cC
    cB
    @5
    cA
    clt
    breq2
    cC
    @5
    cA
    clt
    breq2
    ifboth
    impbid1
end
