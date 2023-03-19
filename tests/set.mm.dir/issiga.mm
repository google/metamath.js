include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csiga.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "elfvex.mm"
include "elex.mm"
include "jca.mm"
include "a1i.mm"
include "simpr1.mm"
include "syl.mm"
include "anc2ri.mm"
include "wb.mm"
include "df-siga.mm"
include "sigaex.mm"
include "wceq.mm"
include "pweq.mm"
include "sseq2d.mm"
include "sseq1.mm"
include "sylan9bb.mm"
include "eleq12.mm"
include "simpr.mm"
include "difeq1.mm"
include "adantr.mm"
include "eleq1d.mm"
include "eleq2.mm"
include "adantl.mm"
include "bitrd.mm"
include "raleqbidv.mm"
include "imbi2d.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "abfmpel.mm"
include "pm5.21ndd.mm"

theorem issiga
  let vx: setvar x
  let cS: class S
  let cO: class O
  let vo: setvar o
  let vs: setvar s

  disjoint O x
  disjoint S x
  disjoint o s
  disjoint o x
  disjoint O o
  disjoint s x
  disjoint O s
  disjoint S o
  disjoint S s
  assert |- ( S e. _V -> ( S e. ( sigAlgebra ` O ) <-> ( S C_ ~P O /\ ( O e. S /\ A. x e. S ( O \ x ) e. S /\ A. x e. ~P S ( x ~<_ _om -> U. x e. S ) ) ) ) )

  proof
    cS
    cvv
    wcel
    #
    cO
    cvv
    wcel
    #
    @0
    wa
    #
    cS
    cO
    csiga
    cfv
    #
    wcel
    #
    cS
    cO
    cpw
    #
    wss
    #
    cO
    cS
    wcel
    #
    cO
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
    @8
    com
    cdom
    wbr
    #
    @8
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
    @4
    @2
    wi
    @0
    @4
    @1
    @0
    cS
    cO
    csiga
    elfvex
    cS
    @3
    elex
    jca
    a1i
    @0
    @19
    @1
    @19
    @1
    wi
    @0
    @19
    @7
    @1
    @6
    @7
    @11
    @17
    simpr1
    cO
    cS
    elex
    syl
    a1i
    anc2ri
    @2
    @4
    @19
    wb
    wi
    @0
    vs
    cv
    #
    vo
    cv
    #
    cpw
    #
    wss
    #
    @21
    @20
    wcel
    #
    @21
    @8
    cdif
    #
    @20
    wcel
    #
    vx
    @20
    wral
    #
    @12
    @13
    @20
    wcel
    #
    wi
    #
    vx
    @20
    cpw
    #
    wral
    #
    w3a
    #
    wa
    @19
    vo
    vs
    cO
    cS
    csiga
    cvv
    cvv
    vx
    vo
    vs
    df-siga
    vx
    vo
    vs
    sigaex
    @21
    cO
    wceq
    #
    @20
    cS
    wceq
    #
    wa
    #
    @23
    @6
    @32
    @18
    @33
    @23
    @20
    @5
    wss
    @34
    @6
    @33
    @22
    @5
    @20
    @21
    cO
    pweq
    sseq2d
    @20
    cS
    @5
    sseq1
    sylan9bb
    @35
    @24
    @7
    @27
    @11
    @31
    @17
    @21
    cO
    @20
    cS
    eleq12
    @35
    @26
    @10
    vx
    @20
    cS
    @33
    @34
    simpr
    @35
    @26
    @9
    @20
    wcel
    #
    @10
    @35
    @25
    @9
    @20
    @33
    @25
    @9
    wceq
    @34
    @21
    cO
    @8
    difeq1
    adantr
    eleq1d
    @34
    @36
    @10
    wb
    @33
    @20
    cS
    @9
    eleq2
    adantl
    bitrd
    raleqbidv
    @34
    @31
    @17
    wb
    @33
    @34
    @29
    @15
    vx
    @30
    @16
    @20
    cS
    pweq
    @34
    @28
    @14
    @12
    @20
    cS
    @13
    eleq2
    imbi2d
    raleqbidv
    adantl
    3anbi123d
    anbi12d
    abfmpel
    a1i
    pm5.21ndd
end
