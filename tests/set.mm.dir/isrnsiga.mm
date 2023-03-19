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
include "sigaex.mm"
include "wceq.mm"
include "sseq1.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "pweq.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "abfmpunirn.mm"
include "rexv.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem isrnsiga
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
    vx
    vo
    vs
    sigaex
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
    @29
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
    @29
    @25
    @12
    vx
    @26
    @13
    @19
    cS
    pweq
    @29
    @24
    @11
    @9
    @19
    cS
    @10
    eleq2
    imbi2d
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
