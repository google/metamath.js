include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cun.mm"
include "wceq.mm"
include "uniprg.mm"
include "3adant1.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cdif.mm"
include "wss.mm"
include "isrnsigau.mm"
include "simprd.mm"
include "simp3d.mm"
include "3ad2ant1.mm"
include "prct.mm"
include "wa.mm"
include "prelpwi.mm"
include "breq1.mm"
include "unieq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mp2d.mm"
include "eqeltrrd.mm"

theorem unelsiga
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x


  assert |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) -> ( A u. B ) e. S )

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
    cpr
    #
    cuni
    #
    cA
    cB
    cun
    #
    cS
    @1
    @2
    @5
    @6
    wceq
    @0
    cA
    cB
    cS
    cS
    uniprg
    3adant1
    @3
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @7
    cuni
    #
    cS
    wcel
    #
    wi
    #
    vx
    cS
    cpw
    #
    wral
    #
    @4
    com
    cdom
    wbr
    #
    @5
    cS
    wcel
    #
    @0
    @1
    @13
    @2
    @0
    cS
    cuni
    #
    cS
    wcel
    #
    @16
    @7
    cdif
    cS
    wcel
    vx
    cS
    wral
    #
    @13
    @0
    cS
    @16
    cpw
    wss
    @17
    @18
    @13
    w3a
    vx
    cS
    isrnsigau
    simprd
    simp3d
    3ad2ant1
    @1
    @2
    @14
    @0
    cA
    cB
    cS
    cS
    prct
    3adant1
    @1
    @2
    @13
    @14
    @15
    wi
    #
    wi
    #
    @0
    @1
    @2
    wa
    @4
    @12
    wcel
    @20
    cA
    cB
    cS
    prelpwi
    @11
    @19
    vx
    @4
    @12
    @7
    @4
    wceq
    #
    @8
    @14
    @10
    @15
    @7
    @4
    com
    cdom
    breq1
    @21
    @9
    @5
    cS
    @7
    @4
    unieq
    eleq1d
    imbi12d
    rspcv
    syl
    3adant1
    mp2d
    eqeltrrd
end
