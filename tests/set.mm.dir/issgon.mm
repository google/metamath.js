include "csiga.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "cvv.mm"
include "elex.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "issiga.mm"
include "elpwuni.mm"
include "biimpa.mm"
include "ancom.mm"
include "eqcom.mm"
include "3imtr4i.mm"
include "3ad2antr1.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "jca.mm"
include "wex.mm"
include "isrnsiga.mm"
include "simprbi.mm"
include "wb.mm"
include "pweq.mm"
include "sseq2d.mm"
include "eleq1.mm"
include "difeq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "3anbi12d.mm"
include "anbi12d.mm"
include "syl.mm"
include "ibi.mm"
include "exlimiv.mm"
include "simprd.mm"
include "biimprd.mm"
include "pwuni.mm"
include "syl5sseqr.mm"
include "jctild.mm"
include "anim2d.mm"
include "biimpar.mm"
include "syl56.mm"
include "impcom.mm"
include "impbii.mm"

theorem issgon
  let cS: class S
  let cO: class O
  let vo: setvar o
  let vx: setvar x


  assert |- ( S e. ( sigAlgebra ` O ) <-> ( S e. U. ran sigAlgebra /\ O = U. S ) )

  proof
    cS
    cO
    csiga
    cfv
    #
    wcel
    #
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cO
    cS
    cuni
    #
    wceq
    #
    wa
    @1
    @3
    @5
    @0
    @2
    cS
    csiga
    cO
    fvssunirn
    sseli
    cS
    cvv
    wcel
    #
    @1
    @5
    cS
    @0
    elex
    @6
    @1
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
    @10
    com
    cdom
    wbr
    @10
    cuni
    cS
    wcel
    wi
    vx
    cS
    cpw
    wral
    #
    w3a
    #
    wa
    #
    @5
    vx
    cS
    cO
    issiga
    #
    @8
    @13
    @9
    @5
    @14
    @9
    @8
    wa
    @4
    cO
    wceq
    #
    @8
    @9
    wa
    @5
    @9
    @8
    @18
    cS
    cO
    elpwuni
    biimpa
    @8
    @9
    ancom
    cO
    @4
    eqcom
    3imtr4i
    3ad2antr1
    syl6bi
    mpcom
    jca
    @5
    @3
    @1
    @3
    @6
    @4
    cS
    wcel
    #
    @4
    @10
    cdif
    #
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @14
    w3a
    #
    wa
    @5
    @6
    @16
    wa
    @1
    @3
    @6
    @23
    cS
    @2
    elex
    @3
    cS
    @4
    cpw
    #
    wss
    #
    @23
    @3
    cS
    vo
    cv
    #
    cpw
    #
    wss
    #
    @26
    cS
    wcel
    #
    @26
    @10
    cdif
    #
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @14
    w3a
    #
    wa
    #
    vo
    wex
    #
    @25
    @23
    wa
    #
    @3
    @6
    @35
    vx
    cS
    vo
    isrnsiga
    simprbi
    @34
    @36
    vo
    @34
    @36
    @34
    @26
    @4
    wceq
    #
    @34
    @36
    wb
    @28
    @32
    @29
    @37
    @14
    @29
    @28
    wa
    @4
    @26
    wceq
    #
    @28
    @29
    wa
    @37
    @29
    @28
    @38
    cS
    @26
    elpwuni
    biimpa
    @28
    @29
    ancom
    @26
    @4
    eqcom
    3imtr4i
    3ad2antr1
    @37
    @28
    @25
    @33
    @23
    @37
    @27
    @24
    cS
    @26
    @4
    pweq
    sseq2d
    @37
    @29
    @19
    @32
    @22
    @14
    @26
    @4
    cS
    eleq1
    @37
    @31
    @21
    vx
    cS
    @37
    @30
    @20
    cS
    @26
    @4
    @10
    difeq1
    eleq1d
    ralbidv
    3anbi12d
    anbi12d
    syl
    ibi
    exlimiv
    syl
    simprd
    jca
    @5
    @23
    @16
    @6
    @5
    @23
    @15
    @8
    @5
    @15
    @23
    @5
    @9
    @19
    @13
    @22
    @14
    cO
    @4
    cS
    eleq1
    @5
    @12
    @21
    vx
    cS
    @5
    @11
    @20
    cS
    cO
    @4
    @10
    difeq1
    eleq1d
    ralbidv
    3anbi12d
    biimprd
    @5
    @24
    cS
    @7
    cS
    pwuni
    cO
    @4
    pweq
    syl5sseqr
    jctild
    anim2d
    @6
    @1
    @16
    @17
    biimpar
    syl56
    impcom
    impbii
end
