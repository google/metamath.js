include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "cab.mm"
include "csiga.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "df-rab.mm"
include "selpw.mm"
include "anbi1i.mm"
include "abbii.mm"
include "eqtri.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "syl5eqelr.mm"
include "pweq.mm"
include "sseq2d.mm"
include "eleq1.mm"
include "difeq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "3anbi12d.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "df-siga.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem sigaval
  let vx: setvar x
  let cO: class O
  let vs: setvar s
  let vo: setvar o

  disjoint s x
  disjoint O s
  disjoint O x
  disjoint o s
  disjoint o x
  disjoint O o
  assert |- ( O e. _V -> ( sigAlgebra ` O ) = { s | ( s C_ ~P O /\ ( O e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( x ~<_ _om -> U. x e. s ) ) ) } )

  proof
    cO
    cvv
    wcel
    #
    vs
    cv
    #
    cO
    cpw
    #
    wss
    #
    cO
    @1
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @1
    wcel
    #
    vx
    @1
    wral
    #
    @5
    com
    cdom
    wbr
    @5
    cuni
    @1
    wcel
    wi
    vx
    @1
    cpw
    wral
    #
    w3a
    #
    wa
    #
    vs
    cab
    #
    cvv
    wcel
    cO
    csiga
    cfv
    @12
    wceq
    @0
    @12
    @10
    vs
    @2
    cpw
    #
    crab
    #
    cvv
    @14
    @1
    @13
    wcel
    #
    @10
    wa
    #
    vs
    cab
    @12
    @10
    vs
    @13
    df-rab
    @16
    @11
    vs
    @15
    @3
    @10
    vs
    @2
    selpw
    anbi1i
    abbii
    eqtri
    @0
    @2
    cvv
    wcel
    @13
    cvv
    wcel
    @14
    cvv
    wcel
    cO
    cvv
    pwexg
    @2
    cvv
    pwexg
    @10
    vs
    @13
    cvv
    rabexg
    3syl
    syl5eqelr
    vo
    cO
    @1
    vo
    cv
    #
    cpw
    #
    wss
    #
    @17
    @1
    wcel
    #
    @17
    @5
    cdif
    #
    @1
    wcel
    #
    vx
    @1
    wral
    #
    @9
    w3a
    #
    wa
    #
    vs
    cab
    @12
    cvv
    cvv
    csiga
    @17
    cO
    wceq
    #
    @25
    @11
    vs
    @26
    @19
    @3
    @24
    @10
    @26
    @18
    @2
    @1
    @17
    cO
    pweq
    sseq2d
    @26
    @20
    @4
    @23
    @8
    @9
    @17
    cO
    @1
    eleq1
    @26
    @22
    @7
    vx
    @1
    @26
    @21
    @6
    @1
    @17
    cO
    @5
    difeq1
    eleq1d
    ralbidv
    3anbi12d
    anbi12d
    abbidv
    vx
    vo
    vs
    df-siga
    fvmptg
    mpdan
end
