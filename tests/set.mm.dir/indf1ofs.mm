include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cind.mm"
include "cfv.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "cv.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cc0.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "wf1.mm"
include "wss.mm"
include "indf1o.mm"
include "f1of1.mm"
include "syl.mm"
include "inss1.mm"
include "f1ores.mm"
include "sylancl.mm"
include "resres.mm"
include "wfn.mm"
include "wceq.mm"
include "f1ofn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "eqidd.mm"
include "wrex.mm"
include "wa.mm"
include "wf.mm"
include "simpll.mm"
include "simpr.mm"
include "sseldi.mm"
include "elpwid.mm"
include "indf.mm"
include "syldan.mm"
include "adantr.mm"
include "feq1d.mm"
include "mpbid.mm"
include "cvv.mm"
include "wb.mm"
include "prex.mm"
include "elmapg.mm"
include "mpan.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "indpi1.mm"
include "inss2.mm"
include "eqeltrd.mm"
include "eqeltrrd.mm"
include "jca.mm"
include "ex.mm"
include "rexlimdva.mm"
include "cdm.mm"
include "cnvimass.mm"
include "biimpa.mm"
include "fdm.mm"
include "adantrr.mm"
include "syl5sseq.mm"
include "simprr.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "indpreima.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "impbid.mm"
include "fvelimab.mm"
include "cnveq.mm"
include "eleq1d.mm"
include "elrab.mm"
include "a1i.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "f1oeq123d.mm"

theorem indf1ofs
  let vf: setvar f
  let cO: class O
  let cV: class V
  let va: setvar a
  let vg: setvar g

  disjoint O f
  disjoint a f
  disjoint a g
  disjoint O a
  disjoint f g
  disjoint O g
  disjoint V a
  disjoint V g
  assert |- ( O e. V -> ( ( _Ind ` O ) |` Fin ) : ( ~P O i^i Fin ) -1-1-onto-> { f e. ( { 0 , 1 } ^m O ) | ( `' f " { 1 } ) e. Fin } )

  proof
    cO
    cV
    wcel
    #
    cO
    cpw
    #
    cfn
    cin
    #
    cO
    cind
    cfv
    #
    @2
    cima
    #
    @3
    @2
    cres
    #
    wf1o
    #
    @2
    vf
    cv
    #
    ccnv
    #
    c1
    csn
    #
    cima
    #
    cfn
    wcel
    #
    vf
    cc0
    c1
    cpr
    #
    cO
    cmap
    co
    #
    crab
    #
    @3
    cfn
    cres
    #
    wf1o
    @0
    @1
    @13
    @3
    wf1
    #
    @2
    @1
    wss
    #
    @6
    @0
    @1
    @13
    @3
    wf1o
    #
    @16
    cO
    cV
    indf1o
    #
    @1
    @13
    @3
    f1of1
    syl
    @1
    cfn
    inss1
    #
    @1
    @13
    @2
    @3
    f1ores
    sylancl
    @0
    @2
    @2
    @4
    @14
    @5
    @15
    @0
    @5
    @3
    @1
    cres
    #
    cfn
    cres
    @15
    @3
    @1
    cfn
    resres
    @0
    @21
    @3
    cfn
    @0
    @18
    @3
    @1
    wfn
    #
    @21
    @3
    wceq
    @19
    @1
    @13
    @3
    f1ofn
    #
    @1
    @3
    fnresdm
    3syl
    reseq1d
    syl5eqr
    @0
    @2
    eqidd
    @0
    vg
    @4
    @14
    @0
    va
    cv
    #
    @3
    cfv
    #
    vg
    cv
    #
    wceq
    #
    va
    @2
    wrex
    #
    @26
    @13
    wcel
    #
    @26
    ccnv
    #
    @9
    cima
    #
    cfn
    wcel
    #
    wa
    #
    @26
    @4
    wcel
    #
    @26
    @14
    wcel
    #
    @0
    @28
    @33
    @0
    @27
    @33
    va
    @2
    @0
    @24
    @2
    wcel
    #
    wa
    #
    @27
    @33
    @37
    @27
    wa
    #
    @29
    @32
    @38
    @0
    cO
    @12
    @26
    wf
    #
    @29
    @0
    @36
    @27
    simpll
    @38
    cO
    @12
    @25
    wf
    #
    @39
    @37
    @40
    @27
    @0
    @36
    @24
    cO
    wss
    #
    @40
    @37
    @24
    cO
    @37
    @2
    @1
    @24
    @20
    @0
    @36
    simpr
    #
    sseldi
    elpwid
    #
    @24
    cO
    cV
    indf
    syldan
    adantr
    @38
    cO
    @12
    @25
    @26
    @37
    @27
    simpr
    #
    feq1d
    mpbid
    @0
    @29
    @39
    @12
    cvv
    wcel
    @0
    @29
    @39
    wb
    cc0
    c1
    prex
    @12
    cO
    @26
    cvv
    cV
    elmapg
    mpan
    #
    biimpar
    syl2anc
    @38
    @25
    ccnv
    #
    @9
    cima
    #
    @31
    cfn
    @38
    @46
    @30
    @9
    @38
    @25
    @26
    @44
    cnveqd
    imaeq1d
    @37
    @47
    cfn
    wcel
    @27
    @37
    @47
    @24
    cfn
    @0
    @36
    @41
    @47
    @24
    wceq
    @43
    @24
    cO
    cV
    indpi1
    syldan
    @37
    @2
    cfn
    @24
    @1
    cfn
    inss2
    @42
    sseldi
    eqeltrd
    adantr
    eqeltrrd
    jca
    ex
    rexlimdva
    @0
    @33
    @28
    @0
    @33
    wa
    #
    @31
    @2
    wcel
    #
    @31
    @3
    cfv
    #
    @26
    wceq
    #
    @28
    @48
    @31
    cO
    wss
    @32
    @49
    @48
    @26
    cdm
    #
    @31
    cO
    @26
    @9
    cnvimass
    @0
    @29
    @52
    cO
    wceq
    #
    @32
    @0
    @29
    wa
    @39
    @53
    @0
    @29
    @39
    @45
    biimpa
    #
    cO
    @12
    @26
    fdm
    syl
    adantrr
    syl5sseq
    @0
    @29
    @32
    simprr
    @31
    cO
    elfpw
    sylanbrc
    @0
    @29
    @51
    @32
    @0
    @29
    @39
    @51
    @54
    @0
    @39
    wa
    @26
    @50
    @26
    cO
    cV
    indpreima
    eqcomd
    syldan
    adantrr
    @27
    @51
    va
    @31
    @2
    @24
    @31
    wceq
    @25
    @50
    @26
    @24
    @31
    @3
    fveq2
    eqeq1d
    rspcev
    syl2anc
    ex
    impbid
    @0
    @22
    @17
    @34
    @28
    wb
    @0
    @18
    @22
    @19
    @23
    syl
    @20
    va
    @1
    @2
    @26
    @3
    fvelimab
    sylancl
    @35
    @33
    wb
    @0
    @11
    @32
    vf
    @26
    @13
    @7
    @26
    wceq
    #
    @10
    @31
    cfn
    @55
    @8
    @30
    @9
    @7
    @26
    cnveq
    imaeq1d
    eleq1d
    elrab
    a1i
    3bitr4d
    eqrdv
    f1oeq123d
    mpbid
end
