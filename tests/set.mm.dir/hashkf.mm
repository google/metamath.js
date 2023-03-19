include "cfn.mm"
include "cn0.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "ccrd.mm"
include "ccom.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "com.mm"
include "cvv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "cardf2.mm"
include "ffun.mm"
include "funco.mm"
include "mp2an.mm"
include "ccnv.mm"
include "cima.mm"
include "dmco.mm"
include "fndm.mm"
include "imaeq2i.mm"
include "wa.mm"
include "wb.mm"
include "funfn.mm"
include "mpbi.mm"
include "elpreima.mm"
include "id.mm"
include "cardid2.mm"
include "ensymd.mm"
include "breq2.mm"
include "rspcev.mm"
include "syl2anr.mm"
include "isfi.mm"
include "sylibr.mm"
include "finnum.mm"
include "ficardom.mm"
include "jca.mm"
include "impbii.mm"
include "bitri.mm"
include "eqriv.mm"
include "3eqtri.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "fveq1i.mm"
include "fvco.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "wf1o.mm"
include "hashgf1o.mm"
include "f1of.mm"
include "ffvelrni.mm"
include "syl.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"

theorem hashkf
  let vx: setvar x
  let cG: class G
  let cK: class K
  let cA: class A
  let vy: setvar y
  assume hashgval.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )
  assume hashkf.2: |- K = ( G o. card )


  assert |- K : Fin --> NN0

  proof
    cfn
    cn0
    cK
    wf
    cK
    cfn
    wfn
    #
    vy
    cv
    #
    cK
    cfv
    #
    cn0
    wcel
    #
    vy
    cfn
    wral
    @0
    cG
    ccrd
    ccom
    #
    cfn
    wfn
    #
    @5
    @4
    wfun
    #
    @4
    cdm
    #
    cfn
    wceq
    cG
    wfun
    #
    ccrd
    wfun
    #
    @6
    cG
    com
    wfn
    #
    @8
    @10
    vx
    cvv
    vx
    cv
    #
    c1
    caddc
    co
    cmpt
    #
    cc0
    crdg
    com
    cres
    #
    com
    wfn
    cc0
    @12
    frfnom
    com
    cG
    @13
    hashgval.1
    fneq1i
    mpbir
    #
    com
    cG
    fnfun
    ax-mp
    @11
    @1
    cen
    wbr
    vx
    con0
    wrex
    vy
    cab
    #
    con0
    ccrd
    wf
    @9
    vy
    vx
    cardf2
    @15
    con0
    ccrd
    ffun
    ax-mp
    #
    cG
    ccrd
    funco
    mp2an
    @7
    ccrd
    ccnv
    #
    cG
    cdm
    #
    cima
    @17
    com
    cima
    #
    cfn
    cG
    ccrd
    dmco
    @18
    com
    @17
    @10
    @18
    com
    wceq
    @14
    com
    cG
    fndm
    ax-mp
    imaeq2i
    vy
    @19
    cfn
    @1
    @19
    wcel
    #
    @1
    ccrd
    cdm
    #
    wcel
    #
    @1
    ccrd
    cfv
    #
    com
    wcel
    #
    wa
    #
    @1
    cfn
    wcel
    #
    ccrd
    @21
    wfn
    #
    @20
    @25
    wb
    @9
    @27
    @16
    ccrd
    funfn
    mpbi
    @21
    @1
    com
    ccrd
    elpreima
    ax-mp
    @25
    @26
    @25
    @1
    @11
    cen
    wbr
    #
    vx
    com
    wrex
    #
    @26
    @24
    @24
    @1
    @23
    cen
    wbr
    #
    @29
    @22
    @24
    id
    @22
    @23
    @1
    @1
    cardid2
    ensymd
    @28
    @30
    vx
    @23
    com
    @11
    @23
    @1
    cen
    breq2
    rspcev
    syl2anr
    vx
    @1
    isfi
    sylibr
    @26
    @22
    @24
    @1
    finnum
    #
    @1
    ficardom
    #
    jca
    impbii
    bitri
    eqriv
    3eqtri
    @4
    cfn
    df-fn
    mpbir2an
    cfn
    cK
    @4
    hashkf.2
    fneq1i
    mpbir
    @3
    vy
    cfn
    @26
    @2
    @23
    cG
    cfv
    #
    cn0
    @26
    @2
    @1
    @4
    cfv
    #
    @33
    @1
    cK
    @4
    hashkf.2
    fveq1i
    @26
    @9
    @22
    @34
    @33
    wceq
    @16
    @31
    @1
    cG
    ccrd
    fvco
    sylancr
    syl5eq
    @26
    @24
    @33
    cn0
    wcel
    @32
    com
    cn0
    @23
    cG
    com
    cn0
    cG
    wf1o
    com
    cn0
    cG
    wf
    vx
    cG
    hashgval.1
    hashgf1o
    com
    cn0
    cG
    f1of
    ax-mp
    ffvelrni
    syl
    eqeltrd
    rgen
    vy
    cfn
    cn0
    cK
    ffnfv
    mpbir2an
end
