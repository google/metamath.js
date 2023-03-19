include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "ssrab2.mm"
include "elpw2.mm"
include "mpbir.mm"
include "wb.mm"
include "wal.mm"
include "nfra1.mm"
include "unissi.mm"
include "sseli.mm"
include "syl6eleqr.mm"
include "rsp.mm"
include "elunirab.mm"
include "syl6ibr.mm"
include "impbid2.mm"
include "alrimi.mm"
include "dfcleq.mm"
include "sylibr.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "anbi1d.mm"
include "nfrab1.mm"
include "nfeq2.mm"
include "eleq2.mm"
include "rabid.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "ralrimi.mm"
include "biantrud.mm"
include "bitr4d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "wi.mm"
include "elpwi.mm"
include "r19.29r.mm"
include "expcom.mm"
include "ssrexv.mm"
include "sylan9r.mm"
include "sylan.mm"
include "biimpar.mm"
include "eluni2.mm"
include "sylib.mm"
include "impel.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "anasss.mm"
include "ancom2s.mm"
include "rexlimiva.mm"
include "impbii.mm"

theorem cover2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume cover2.1: |- B e. _V
  assume cover2.2: |- A = U. B

  disjoint ph x
  disjoint ph z
  disjoint x z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint y z
  disjoint A x
  disjoint A z
  assert |- ( A. x e. A E. y e. B ( x e. y /\ ph ) <-> E. z e. ~P B ( U. z = A /\ A. y e. z ph ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    wph
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    vz
    cv
    #
    cuni
    #
    cA
    wceq
    #
    wph
    vy
    @6
    wral
    #
    wa
    #
    vz
    cB
    cpw
    #
    wrex
    #
    @5
    wph
    vy
    cB
    crab
    #
    @11
    wcel
    #
    @13
    cuni
    #
    cA
    wceq
    #
    @12
    @14
    @13
    cB
    wss
    wph
    vy
    cB
    ssrab2
    #
    @13
    cB
    cover2.1
    elpw2
    mpbir
    @5
    @0
    @15
    wcel
    #
    @0
    cA
    wcel
    #
    wb
    #
    vx
    wal
    @16
    @5
    @20
    vx
    @4
    vx
    cA
    nfra1
    @5
    @18
    @19
    @18
    @0
    cB
    cuni
    #
    cA
    @15
    @21
    @0
    @13
    cB
    @17
    unissi
    sseli
    cover2.2
    syl6eleqr
    @5
    @19
    @4
    @18
    @4
    vx
    cA
    rsp
    wph
    vy
    @0
    cB
    elunirab
    syl6ibr
    impbid2
    alrimi
    vx
    @15
    cA
    dfcleq
    sylibr
    @10
    @16
    vz
    @13
    @11
    @6
    @13
    wceq
    #
    @10
    @16
    @9
    wa
    @16
    @22
    @8
    @16
    @9
    @22
    @7
    @15
    cA
    @6
    @13
    unieq
    eqeq1d
    anbi1d
    @22
    @9
    @16
    @22
    wph
    vy
    @6
    vy
    @6
    @13
    wph
    vy
    cB
    nfrab1
    nfeq2
    @22
    @1
    @6
    wcel
    @1
    @13
    wcel
    #
    wph
    @6
    @13
    @1
    eleq2
    @23
    @1
    cB
    wcel
    wph
    wph
    vy
    cB
    rabid
    simprbi
    syl6bi
    ralrimi
    biantrud
    bitr4d
    rspcev
    sylancr
    @10
    @5
    vz
    @11
    @6
    @11
    wcel
    #
    @9
    @8
    @5
    @24
    @9
    @8
    @5
    @24
    @9
    wa
    #
    @8
    wa
    @4
    vx
    cA
    @25
    @8
    @19
    @4
    @25
    @2
    vy
    @6
    wrex
    #
    @4
    @8
    @19
    wa
    #
    @24
    @6
    cB
    wss
    #
    @9
    @26
    @4
    wi
    @6
    cB
    elpwi
    @9
    @26
    @3
    vy
    @6
    wrex
    #
    @28
    @4
    @26
    @9
    @29
    @2
    wph
    vy
    @6
    r19.29r
    expcom
    @3
    vy
    @6
    cB
    ssrexv
    sylan9r
    sylan
    @27
    @0
    @7
    wcel
    #
    @26
    @8
    @30
    @19
    @7
    cA
    @0
    eleq2
    biimpar
    vy
    @0
    @6
    eluni2
    sylib
    impel
    anassrs
    ralrimiva
    anasss
    ancom2s
    rexlimiva
    impbii
end
