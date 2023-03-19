include "cdmn.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "ccring.mm"
include "dmncrng.mm"
include "crngocom.mm"
include "3adant3r2.mm"
include "3adant3r1.mm"
include "eqeq12d.mm"
include "sylan.mm"
include "adantr.mm"
include "wi.mm"
include "3anrot.mm"
include "biimpri.mm"
include "dmncan1.mm"
include "sylanl2.mm"
include "sylbid.mm"

theorem dmncan2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  assume dmncan.1: |- G = ( 1st ` R )
  assume dmncan.2: |- H = ( 2nd ` R )
  assume dmncan.3: |- X = ran G
  assume dmncan.4: |- Z = ( GId ` G )


  assert |- ( ( ( R e. Dmn /\ ( A e. X /\ B e. X /\ C e. X ) ) /\ C =/= Z ) -> ( ( A H C ) = ( B H C ) -> A = B ) )

  proof
    cR
    cdmn
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cC
    cZ
    wne
    #
    wa
    cA
    cC
    cH
    co
    #
    cB
    cC
    cH
    co
    #
    wceq
    #
    cC
    cA
    cH
    co
    #
    cC
    cB
    cH
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @5
    @9
    @12
    wb
    #
    @6
    @0
    cR
    ccring
    wcel
    #
    @4
    @14
    cR
    dmncrng
    @15
    @4
    wa
    @7
    @10
    @8
    @11
    @15
    @1
    @3
    @7
    @10
    wceq
    @2
    cA
    cC
    cR
    cG
    cH
    cX
    dmncan.1
    dmncan.2
    dmncan.3
    crngocom
    3adant3r2
    @15
    @2
    @3
    @8
    @11
    wceq
    @1
    cB
    cC
    cR
    cG
    cH
    cX
    dmncan.1
    dmncan.2
    dmncan.3
    crngocom
    3adant3r1
    eqeq12d
    sylan
    adantr
    @4
    @0
    @3
    @1
    @2
    w3a
    #
    @6
    @12
    @13
    wi
    @16
    @4
    @3
    @1
    @2
    3anrot
    biimpri
    cC
    cA
    cB
    cR
    cG
    cH
    cX
    cZ
    dmncan.1
    dmncan.2
    dmncan.3
    dmncan.4
    dmncan1
    sylanl2
    sylbid
end
