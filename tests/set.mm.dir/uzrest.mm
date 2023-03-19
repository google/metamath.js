include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "crn.mm"
include "crest.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "cpw.mm"
include "zex.mm"
include "pwex.mm"
include "wf.mm"
include "wss.mm"
include "uzf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "restval.mm"
include "mp2an.mm"
include "wral.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "ineq2i.mm"
include "uzin.mm"
include "ancoms.mm"
include "syl5eq.mm"
include "wfn.mm"
include "ffn.mm"
include "a1i.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "inss2.mm"
include "ifcl.mm"
include "uzid.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "sseldi.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ralrn.mm"
include "sylibr.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "syl5eqss.mm"
include "uztrn2.mm"
include "ex.mm"
include "ssrdv.mm"
include "adantl.mm"
include "df-ss.mm"
include "sseli.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "elrestr.mm"
include "eqeltrrd.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funimass4.mm"
include "eqssd.mm"

theorem uzrest
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume uzfbas.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> ( ran ZZ>= |`t Z ) = ( ZZ>= " Z ) )

  proof
    cM
    cz
    wcel
    #
    cuz
    crn
    #
    cZ
    crest
    co
    #
    cuz
    cZ
    cima
    #
    @0
    @2
    vx
    @1
    vx
    cv
    #
    cZ
    cin
    #
    cmpt
    #
    crn
    #
    @3
    @1
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    @2
    @7
    wceq
    @1
    cz
    cpw
    #
    cz
    zex
    pwex
    cz
    @10
    cuz
    wf
    #
    @1
    @10
    wss
    uzf
    cz
    @10
    cuz
    frn
    ax-mp
    ssexi
    #
    cZ
    cM
    cuz
    cfv
    #
    cvv
    uzfbas.1
    cM
    cuz
    fvex
    eqeltri
    #
    vx
    cZ
    @1
    cvv
    cvv
    restval
    mp2an
    @0
    @1
    @3
    @6
    wf
    #
    @7
    @3
    wss
    @0
    @5
    @3
    wcel
    #
    vx
    @1
    wral
    #
    @15
    @0
    vy
    cv
    #
    cuz
    cfv
    #
    cZ
    cin
    #
    @3
    wcel
    #
    vy
    cz
    wral
    #
    @17
    @0
    @21
    vy
    cz
    @0
    @18
    cz
    wcel
    #
    wa
    #
    @20
    @18
    cM
    cle
    wbr
    #
    cM
    @18
    cif
    #
    cuz
    cfv
    #
    @3
    @24
    @20
    @19
    @13
    cin
    #
    @27
    cZ
    @13
    @19
    uzfbas.1
    ineq2i
    @23
    @0
    @28
    @27
    wceq
    @18
    cM
    uzin
    ancoms
    syl5eq
    #
    @24
    cuz
    cz
    wfn
    #
    cZ
    cz
    wss
    #
    @26
    cZ
    wcel
    @27
    @3
    wcel
    @30
    @24
    @11
    @30
    uzf
    cz
    @10
    cuz
    ffn
    ax-mp
    #
    a1i
    @31
    @24
    cZ
    @13
    cz
    uzfbas.1
    cM
    uzssz
    eqsstri
    #
    a1i
    @24
    @20
    cZ
    @26
    @19
    cZ
    inss2
    @24
    @26
    @27
    @20
    @24
    @26
    cz
    wcel
    @26
    @27
    wcel
    @25
    cM
    @18
    cz
    ifcl
    @26
    uzid
    syl
    @29
    eleqtrrd
    sseldi
    cz
    cZ
    cuz
    @26
    fnfvima
    syl3anc
    eqeltrd
    ralrimiva
    @30
    @17
    @22
    wb
    @32
    @16
    @21
    vx
    vy
    cz
    cuz
    @4
    @19
    wceq
    @5
    @20
    @3
    @4
    @19
    cZ
    ineq1
    eleq1d
    ralrn
    ax-mp
    sylibr
    vx
    @1
    @3
    @5
    @6
    @6
    eqid
    fmpt
    sylib
    @1
    @3
    @6
    frn
    syl
    syl5eqss
    @0
    @4
    cuz
    cfv
    #
    @2
    wcel
    #
    vx
    cZ
    wral
    #
    @3
    @2
    wss
    #
    @0
    @35
    vx
    cZ
    @0
    @4
    cZ
    wcel
    #
    wa
    #
    @34
    cZ
    cin
    #
    @34
    @2
    @39
    @34
    cZ
    wss
    #
    @40
    @34
    wceq
    @38
    @41
    @0
    @38
    vy
    @34
    cZ
    @38
    @18
    @34
    wcel
    @18
    cZ
    wcel
    cM
    @18
    @4
    cZ
    uzfbas.1
    uztrn2
    ex
    ssrdv
    adantl
    @34
    cZ
    df-ss
    sylib
    @39
    @8
    @9
    @34
    @1
    wcel
    #
    @40
    @2
    wcel
    @8
    @39
    @12
    a1i
    @9
    @39
    @14
    a1i
    @39
    @30
    @4
    cz
    wcel
    #
    @42
    @32
    @38
    @43
    @0
    cZ
    cz
    @4
    @33
    sseli
    adantl
    cz
    @4
    cuz
    fnfvelrn
    sylancr
    @34
    cZ
    @1
    cvv
    cvv
    elrestr
    syl3anc
    eqeltrrd
    ralrimiva
    cuz
    wfun
    #
    cZ
    cuz
    cdm
    #
    wss
    @37
    @36
    wb
    @11
    @44
    uzf
    cz
    @10
    cuz
    ffun
    ax-mp
    cZ
    cz
    @45
    @33
    cz
    @10
    cuz
    uzf
    fdmi
    sseqtr4i
    vx
    cZ
    @2
    cuz
    funimass4
    mp2an
    sylibr
    eqssd
end
