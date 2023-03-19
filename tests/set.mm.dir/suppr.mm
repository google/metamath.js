include "wor.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "wbr.mm"
include "cif.mm"
include "simp1.mm"
include "ifcl.mm"
include "3adant1.mm"
include "ifpr.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "wceq.mm"
include "breq1.mm"
include "notbid.mm"
include "sonr.mm"
include "3adant3.mm"
include "adantr.mm"
include "simpr.mm"
include "ifbothda.mm"
include "wa.mm"
include "wi.mm"
include "so2nr.mm"
include "3impb.mm"
include "3com23.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "3adant2.mm"
include "wb.mm"
include "breq2.mm"
include "ralprg.mm"
include "mpbir2and.mm"
include "r19.21bi.mm"
include "supmax.mm"

theorem suppr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vy: setvar y


  assert |- ( ( R Or A /\ B e. A /\ C e. A ) -> sup ( { B , C } , A , R ) = if ( C R B , B , C ) )

  proof
    cA
    cR
    wor
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    w3a
    #
    vy
    cA
    cB
    cC
    cpr
    #
    cC
    cB
    cR
    wbr
    #
    cB
    cC
    cif
    #
    cR
    @0
    @1
    @2
    simp1
    @1
    @2
    @6
    cA
    wcel
    @0
    @5
    cB
    cC
    cA
    ifcl
    3adant1
    @1
    @2
    @6
    @4
    wcel
    @0
    @5
    cB
    cC
    cA
    cA
    ifpr
    3adant1
    @3
    @6
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    @4
    @3
    @9
    vy
    @4
    wral
    #
    @6
    cB
    cR
    wbr
    #
    wn
    #
    @6
    cC
    cR
    wbr
    #
    wn
    #
    @5
    cB
    cB
    cR
    wbr
    #
    wn
    #
    @5
    wn
    #
    @12
    @3
    cB
    cC
    cB
    @6
    wceq
    #
    @15
    @11
    cB
    @6
    cB
    cR
    breq1
    notbid
    cC
    @6
    wceq
    #
    @5
    @11
    cC
    @6
    cB
    cR
    breq1
    notbid
    @3
    @16
    @5
    @0
    @1
    @16
    @2
    cA
    cB
    cR
    sonr
    3adant3
    adantr
    @3
    @17
    simpr
    ifbothda
    @5
    cB
    cC
    cR
    wbr
    #
    wn
    #
    cC
    cC
    cR
    wbr
    #
    wn
    #
    @14
    @3
    cB
    cC
    @18
    @20
    @13
    cB
    @6
    cC
    cR
    breq1
    notbid
    @19
    @22
    @13
    cC
    @6
    cC
    cR
    breq1
    notbid
    @3
    @5
    @21
    @3
    @5
    @20
    wa
    wn
    #
    @5
    @21
    wi
    @0
    @2
    @1
    @24
    @0
    @2
    @1
    @24
    cA
    cC
    cB
    cR
    so2nr
    3impb
    3com23
    @5
    @20
    imnan
    sylibr
    imp
    @3
    @23
    @17
    @0
    @2
    @23
    @1
    cA
    cC
    cR
    sonr
    3adant2
    adantr
    ifbothda
    @1
    @2
    @10
    @12
    @14
    wa
    wb
    @0
    @9
    @12
    @14
    vy
    cB
    cC
    cA
    cA
    @7
    cB
    wceq
    @8
    @11
    @7
    cB
    @6
    cR
    breq2
    notbid
    @7
    cC
    wceq
    @8
    @13
    @7
    cC
    @6
    cR
    breq2
    notbid
    ralprg
    3adant1
    mpbir2and
    r19.21bi
    supmax
end
