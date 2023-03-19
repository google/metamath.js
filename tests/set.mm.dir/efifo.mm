include "cr.mm"
include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wf.mm"
include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "wcel.mm"
include "cabs.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cc.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efcl.mm"
include "syl.mm"
include "absefi.mm"
include "wa.mm"
include "wb.mm"
include "absf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "fmpti.mm"
include "ax-mp.mm"
include "wss.mm"
include "frn.mm"
include "cc0.mm"
include "c2.mm"
include "cpi.mm"
include "cioc.mm"
include "cres.mm"
include "df-ima.mm"
include "cmpt.mm"
include "reseq1i.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "ssriv.mm"
include "resmpt.mm"
include "eqtri.mm"
include "rneqi.mm"
include "wf1o.mm"
include "0re.mm"
include "eqid.mm"
include "caddc.mm"
include "recni.mm"
include "addid2i.mm"
include "oveq2i.mm"
include "eqcomi.mm"
include "efif1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "imassrn.mm"
include "eqsstr3i.mm"
include "eqssi.mm"
include "df-fo.mm"
include "mpbir2an.mm"

theorem efifo
  let vz: setvar z
  let cC: class C
  let cF: class F
  assume efifo.1: |- F = ( z e. RR |-> ( exp ` ( _i x. z ) ) )
  assume efifo.2: |- C = ( `' abs " { 1 } )

  disjoint C z
  assert |- F : RR -onto-> C

  proof
    cr
    cC
    cF
    wfo
    cF
    cr
    wfn
    #
    cF
    crn
    #
    cC
    wceq
    cr
    cC
    cF
    wf
    #
    @0
    vz
    cr
    cC
    ci
    vz
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cF
    efifo.1
    @3
    cr
    wcel
    #
    @5
    cabs
    ccnv
    c1
    csn
    cima
    #
    cC
    @6
    @5
    cc
    wcel
    #
    @5
    cabs
    cfv
    c1
    wceq
    #
    @5
    @7
    wcel
    #
    @6
    @4
    cc
    wcel
    #
    @8
    @6
    ci
    cc
    wcel
    @3
    cc
    wcel
    @11
    ax-icn
    @3
    recn
    ci
    @3
    mulcl
    sylancr
    @4
    efcl
    syl
    @3
    absefi
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @10
    @8
    @9
    wa
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    c1
    @5
    cabs
    fniniseg
    mp2b
    sylanbrc
    efifo.2
    syl6eleqr
    fmpti
    #
    cr
    cC
    cF
    ffn
    ax-mp
    @1
    cC
    @2
    @1
    cC
    wss
    @12
    cr
    cC
    cF
    frn
    ax-mp
    cC
    cF
    cc0
    c2
    cpi
    cmul
    co
    #
    cioc
    co
    #
    cima
    #
    @1
    @15
    cF
    @14
    cres
    #
    crn
    #
    cC
    cF
    @14
    df-ima
    @17
    vz
    @14
    @5
    cmpt
    #
    crn
    #
    cC
    @16
    @18
    @16
    vz
    cr
    @5
    cmpt
    #
    @14
    cres
    #
    @18
    cF
    @20
    @14
    efifo.1
    reseq1i
    @14
    cr
    wss
    @21
    @18
    wceq
    vz
    @14
    cr
    @3
    @14
    wcel
    #
    @6
    cc0
    @3
    clt
    wbr
    #
    @3
    @13
    cle
    wbr
    #
    cc0
    cxr
    wcel
    @13
    cr
    wcel
    @22
    @6
    @23
    @24
    w3a
    wb
    0xr
    c2
    cpi
    2re
    pire
    remulcli
    #
    cc0
    @13
    @3
    elioc2
    mp2an
    simp1bi
    ssriv
    vz
    cr
    @14
    @5
    resmpt
    ax-mp
    eqtri
    rneqi
    @14
    cC
    @18
    wf1o
    #
    @14
    cC
    @18
    wfo
    @19
    cC
    wceq
    cc0
    cr
    wcel
    @26
    0re
    vz
    cc0
    cC
    @14
    @18
    @18
    eqid
    efifo.2
    cc0
    cc0
    @13
    caddc
    co
    #
    cioc
    co
    @14
    @27
    @13
    cc0
    cioc
    @13
    @13
    @25
    recni
    addid2i
    oveq2i
    eqcomi
    efif1o
    ax-mp
    @14
    cC
    @18
    f1ofo
    @14
    cC
    @18
    forn
    mp2b
    eqtri
    eqtri
    cF
    @14
    imassrn
    eqsstr3i
    eqssi
    cr
    cC
    cF
    df-fo
    mpbir2an
end
