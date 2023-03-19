include "cdmn.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "cgs.mm"
include "cfv.mm"
include "wceq.mm"
include "crngo.mm"
include "dmnrngo.mm"
include "eqid.mm"
include "rngosubdi.mm"
include "sylan.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "wi.mm"
include "wo.mm"
include "cgr.mm"
include "rngogrpo.mm"
include "syl.mm"
include "grpodivcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "dmnnzd.mm"
include "3exp2.mm"
include "imp31.mm"
include "syldan.mm"
include "exp43.mm"
include "3imp2.mm"
include "neor.mm"
include "syl6ib.mm"
include "com23.mm"
include "imp.mm"
include "sylbird.mm"
include "wb.mm"
include "rngocl.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "grpoeqdivid.mm"
include "syl3anc.mm"
include "3adantr1.mm"
include "3imtr4d.mm"

theorem dmncan1
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


  assert |- ( ( ( R e. Dmn /\ ( A e. X /\ B e. X /\ C e. X ) ) /\ A =/= Z ) -> ( ( A H B ) = ( A H C ) -> B = C ) )

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
    cA
    cZ
    wne
    #
    wa
    #
    cA
    cB
    cH
    co
    #
    cA
    cC
    cH
    co
    #
    cG
    cgs
    cfv
    #
    co
    #
    cZ
    wceq
    #
    cB
    cC
    @10
    co
    #
    cZ
    wceq
    #
    @8
    @9
    wceq
    #
    cB
    cC
    wceq
    #
    @7
    @12
    cA
    @13
    cH
    co
    #
    cZ
    wceq
    #
    @14
    @7
    @17
    @11
    cZ
    @5
    @17
    @11
    wceq
    #
    @6
    @0
    cR
    crngo
    wcel
    #
    @4
    @19
    cR
    dmnrngo
    #
    cA
    cB
    cC
    @10
    cR
    cG
    cH
    cX
    dmncan.1
    dmncan.2
    dmncan.3
    @10
    eqid
    #
    rngosubdi
    sylan
    adantr
    eqeq1d
    @5
    @6
    @18
    @14
    wi
    @5
    @18
    @6
    @14
    @5
    @18
    cA
    cZ
    wceq
    @14
    wo
    #
    @6
    @14
    wi
    @0
    @1
    @2
    @3
    @18
    @23
    wi
    #
    @0
    @1
    @2
    @3
    @24
    @0
    @1
    wa
    @2
    @3
    wa
    #
    @13
    cX
    wcel
    #
    @24
    @0
    @25
    @26
    @1
    @0
    cG
    cgr
    wcel
    #
    @25
    @26
    @0
    @20
    @27
    @21
    cR
    cG
    dmncan.1
    rngogrpo
    syl
    #
    @27
    @2
    @3
    @26
    cB
    cC
    @10
    cG
    cX
    dmncan.3
    @22
    grpodivcl
    3expb
    sylan
    adantlr
    @0
    @1
    @26
    @24
    @0
    @1
    @26
    @18
    @23
    cA
    @13
    cR
    cG
    cH
    cX
    cZ
    dmncan.1
    dmncan.2
    dmncan.3
    dmncan.4
    dmnnzd
    3exp2
    imp31
    syldan
    exp43
    3imp2
    @14
    cA
    cZ
    neor
    syl6ib
    com23
    imp
    sylbird
    @5
    @15
    @12
    wb
    #
    @6
    @5
    @27
    @8
    cX
    wcel
    #
    @9
    cX
    wcel
    #
    @29
    @0
    @27
    @4
    @28
    adantr
    @0
    @20
    @4
    @30
    @21
    @20
    @1
    @2
    @30
    @3
    cA
    cB
    cR
    cG
    cH
    cX
    dmncan.1
    dmncan.2
    dmncan.3
    rngocl
    3adant3r3
    sylan
    @0
    @20
    @4
    @31
    @21
    @20
    @1
    @3
    @31
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
    rngocl
    3adant3r2
    sylan
    @8
    @9
    @10
    cZ
    cG
    cX
    dmncan.3
    dmncan.4
    @22
    grpoeqdivid
    syl3anc
    adantr
    @5
    @16
    @14
    wb
    #
    @6
    @0
    @2
    @3
    @32
    @1
    @0
    @27
    @25
    @32
    @28
    @27
    @2
    @3
    @32
    cB
    cC
    @10
    cZ
    cG
    cX
    dmncan.3
    dmncan.4
    @22
    grpoeqdivid
    3expb
    sylan
    3adantr1
    adantr
    3imtr4d
end
