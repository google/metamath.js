include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "w3a.mm"
include "cdif.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "simp2.mm"
include "elssuni.mm"
include "difin2.mm"
include "3syl.mm"
include "cv.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "isrnsigau.mm"
include "simprd.mm"
include "simp2d.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "3adant2.mm"
include "intprg.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "c0.mm"
include "wne.mm"
include "simp1.mm"
include "prssi.mm"
include "prex.mm"
include "elpw.mm"
include "sylibr.mm"
include "prct.mm"
include "prnzg.mm"
include "syl.mm"
include "sigaclci.mm"
include "syl22anc.mm"
include "eqeltrd.mm"

theorem difelsiga
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x


  assert |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) -> ( A \ B ) e. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    #
    cA
    cB
    cdif
    #
    cS
    cuni
    #
    cB
    cdif
    #
    cA
    cpr
    #
    cint
    #
    cS
    @3
    @4
    @6
    cA
    cin
    #
    @8
    @3
    @1
    cA
    @5
    wss
    @4
    @9
    wceq
    @0
    @1
    @2
    simp2
    #
    cA
    cS
    elssuni
    cA
    cB
    @5
    difin2
    3syl
    @3
    @6
    cS
    wcel
    #
    @1
    @8
    @9
    wceq
    @0
    @2
    @11
    @1
    @0
    @5
    vx
    cv
    #
    cdif
    #
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @2
    @11
    @0
    @5
    cS
    wcel
    #
    @15
    @12
    com
    cdom
    wbr
    @12
    cuni
    cS
    wcel
    wi
    vx
    cS
    cpw
    #
    wral
    #
    @0
    cS
    @5
    cpw
    wss
    @16
    @15
    @18
    w3a
    vx
    cS
    isrnsigau
    simprd
    simp2d
    @14
    @11
    vx
    cB
    cS
    @12
    cB
    wceq
    @13
    @6
    cS
    @12
    cB
    @5
    difeq2
    eleq1d
    rspccva
    sylan
    3adant2
    #
    @10
    @6
    cA
    cS
    cS
    intprg
    syl2anc
    eqtr4d
    @3
    @0
    @7
    @17
    wcel
    #
    @7
    com
    cdom
    wbr
    #
    @7
    c0
    wne
    #
    @8
    cS
    wcel
    @0
    @1
    @2
    simp1
    @3
    @7
    cS
    wss
    #
    @20
    @3
    @11
    @1
    @23
    @19
    @10
    @6
    cA
    cS
    prssi
    syl2anc
    @7
    cS
    @6
    cA
    prex
    elpw
    sylibr
    @3
    @11
    @1
    @21
    @19
    @10
    @6
    cA
    cS
    cS
    prct
    syl2anc
    @3
    @11
    @22
    @19
    @6
    cA
    cS
    prnzg
    syl
    @7
    cS
    sigaclci
    syl22anc
    eqeltrd
end
