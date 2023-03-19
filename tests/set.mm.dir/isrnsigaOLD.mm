include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "wss.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "df-siga.mm"
include "cab.mm"
include "crab.mm"
include "df-rab.mm"
include "wb.mm"
include "vex.mm"
include "elpwg.mm"
include "ax-mp.mm"
include "anbi1i.mm"
include "abbii.mm"
include "eqtr2i.mm"
include "grothpwex.mm"
include "pwex.mm"
include "rabex.mm"
include "eqeltri.mm"
include "wceq.mm"
include "sseq1.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "pweq.mm"
include "biidd.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "abfmpunirn.mm"
include "rexv.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem isrnsigaOLD
  let vx: setvar x
  let cS: class S
  let vo: setvar o
  let vs: setvar s

  disjoint o x
  disjoint S o
  disjoint S x
  disjoint o s
  disjoint s x
  disjoint S s
  assert |- ( S e. U. ran sigAlgebra <-> ( S e. _V /\ E. o ( S C_ ~P o /\ ( o e. S /\ A. x e. S ( o \ x ) e. S /\ A. x e. ~P S ( x ~<_ _om -> U. x e. S ) ) ) ) )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    cS
    cvv
    wcel
    #
    cS
    vo
    cv
    #
    cpw
    #
    wss
    #
    @1
    cS
    wcel
    #
    @1
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
    @5
    com
    cdom
    wbr
    #
    @5
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
    w3a
    #
    wa
    #
    vo
    cvv
    wrex
    #
    wa
    @0
    @16
    vo
    wex
    #
    wa
    vs
    cv
    #
    @2
    wss
    #
    @1
    @19
    wcel
    #
    @6
    @19
    wcel
    #
    vx
    @19
    wral
    #
    @9
    @10
    @19
    wcel
    #
    wi
    #
    vx
    @19
    cpw
    #
    wral
    #
    w3a
    #
    wa
    #
    @16
    vo
    vs
    cS
    csiga
    cvv
    vx
    vo
    vs
    df-siga
    @29
    vs
    cab
    #
    @28
    vs
    @2
    cpw
    #
    crab
    #
    cvv
    @32
    @19
    @31
    wcel
    #
    @28
    wa
    #
    vs
    cab
    @30
    @28
    vs
    @31
    df-rab
    @34
    @29
    vs
    @33
    @20
    @28
    @19
    cvv
    wcel
    @33
    @20
    wb
    vs
    vex
    @19
    @2
    cvv
    elpwg
    ax-mp
    anbi1i
    abbii
    eqtr2i
    @28
    vs
    @31
    @2
    vo
    grothpwex
    pwex
    rabex
    eqeltri
    @19
    cS
    wceq
    #
    @20
    @3
    @28
    @15
    @19
    cS
    @2
    sseq1
    @35
    @21
    @4
    @23
    @8
    @27
    @14
    @19
    cS
    @1
    eleq2
    @22
    @7
    vx
    @19
    cS
    @19
    cS
    @6
    eleq2
    raleqbi1dv
    @35
    @25
    @12
    vx
    @26
    @13
    @19
    cS
    pweq
    @35
    @9
    @9
    @24
    @11
    @35
    @9
    biidd
    @19
    cS
    @10
    eleq2
    imbi12d
    raleqbidv
    3anbi123d
    anbi12d
    abfmpunirn
    @17
    @18
    @0
    @16
    vo
    rexv
    anbi2i
    bitri
end
