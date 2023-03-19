include "wcel.mm"
include "cv.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wel.mm"
include "wn.mm"
include "wral.mm"
include "wss.mm"
include "w3a.mm"
include "cab.mm"
include "cuni.mm"
include "wceq.mm"
include "untelirr.mm"
include "wrex.mm"
include "eluni2.mm"
include "vex.mm"
include "sseq1.mm"
include "treq.mm"
include "raleq.mm"
include "3anbi123d.mm"
include "elab.mm"
include "elequ1.mm"
include "elequ2.mm"
include "bitrd.mm"
include "notbid.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "rsp.mm"
include "syl.mm"
include "rexlimiv.mm"
include "mprg.mm"
include "dfon2lem2.mm"
include "dfpss2.mm"
include "dfon2lem1.mm"
include "cvv.mm"
include "ssexg.mm"
include "mpan.mm"
include "psseq1.mm"
include "anbi12d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "imp.mm"
include "sylan.mm"
include "csuc.mm"
include "csn.mm"
include "snssi.mm"
include "cun.mm"
include "unss.mm"
include "df-suc.mm"
include "sseq1i.mm"
include "sylbb2.mm"
include "sylancr.mm"
include "suctr.mm"
include "ax-mp.mm"
include "untuni.mm"
include "mprgbir.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfab.mm"
include "nfuni.mm"
include "untsucf.mm"
include "nfcv.mm"
include "nfsuc.mm"
include "raleqf.mm"
include "cbvabv.mm"
include "elab2g.mm"
include "biimprd.mm"
include "sucexg.mm"
include "syl11.mm"
include "mp3an23.mm"
include "com12.mm"
include "elssuni.mm"
include "sucssel.mm"
include "syl5.mm"
include "syld.mm"
include "mpd.mm"
include "syl6.mm"
include "mpan2i.mm"
include "syl5bir.mm"
include "mpani.mm"
include "mt3i.mm"
include "pm3.2i.mm"
include "mpbii.mm"
include "ex.mm"

theorem dfon2lem3
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cV: class V
  let vw: setvar w
  let vt: setvar t

  disjoint A x
  disjoint A z
  disjoint x z
  disjoint A w
  disjoint A t
  disjoint w x
  disjoint t x
  disjoint w z
  disjoint t z
  disjoint t w
  assert |- ( A e. V -> ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) -> ( Tr A /\ A. z e. A -. z e. z ) ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    cA
    wpss
    #
    @1
    wtr
    #
    wa
    #
    @1
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    cA
    wtr
    #
    vz
    vz
    wel
    #
    wn
    #
    vz
    cA
    wral
    #
    wa
    #
    @0
    @7
    wa
    #
    vw
    cv
    #
    cA
    wss
    #
    @14
    wtr
    #
    vt
    vt
    wel
    #
    wn
    #
    vt
    @14
    wral
    #
    w3a
    #
    vw
    cab
    #
    cuni
    #
    cA
    wceq
    #
    @12
    @13
    @23
    @22
    @22
    wcel
    #
    @10
    @24
    wn
    vz
    @22
    vz
    @22
    untelirr
    vz
    cv
    #
    @22
    wcel
    vz
    vx
    wel
    #
    vx
    @21
    wrex
    @10
    vx
    @25
    @21
    eluni2
    @26
    @10
    vx
    @21
    @1
    @21
    wcel
    #
    @10
    vz
    @1
    wral
    #
    @26
    @10
    wi
    @27
    @1
    cA
    wss
    #
    @3
    @18
    vt
    @1
    wral
    #
    w3a
    #
    @28
    @20
    @31
    vw
    @1
    vx
    vex
    @14
    @1
    wceq
    @15
    @29
    @16
    @3
    @19
    @30
    @14
    @1
    cA
    sseq1
    @14
    @1
    treq
    @18
    vt
    @14
    @1
    raleq
    3anbi123d
    elab
    @30
    @29
    @28
    @3
    @30
    @28
    @18
    @10
    vt
    vz
    @1
    vt
    cv
    @25
    wceq
    #
    @17
    @9
    @32
    @17
    vz
    vt
    wel
    @9
    vt
    vz
    vt
    elequ1
    vt
    vz
    vz
    elequ2
    bitrd
    notbid
    cbvralv
    biimpi
    3ad2ant3
    sylbi
    #
    @10
    vz
    @1
    rsp
    syl
    rexlimiv
    sylbi
    mprg
    @13
    @22
    cA
    wss
    #
    @23
    wn
    #
    @24
    @16
    @19
    vw
    cA
    dfon2lem2
    #
    @34
    @35
    wa
    @22
    cA
    wpss
    #
    @13
    @24
    @22
    cA
    dfpss2
    @13
    @37
    @22
    wtr
    #
    @24
    @15
    @19
    vw
    dfon2lem1
    #
    @13
    @37
    @38
    wa
    #
    @22
    cA
    wcel
    #
    @24
    @0
    @22
    cvv
    wcel
    #
    @7
    @40
    @41
    wi
    #
    @34
    @0
    @42
    @36
    @22
    cA
    cV
    ssexg
    mpan
    @42
    @7
    @43
    @6
    @43
    vx
    @22
    cvv
    @1
    @22
    wceq
    #
    @4
    @40
    @5
    @41
    @44
    @2
    @37
    @3
    @38
    @1
    @22
    cA
    psseq1
    @1
    @22
    treq
    anbi12d
    @1
    @22
    cA
    eleq1
    imbi12d
    spcgv
    imp
    sylan
    @41
    @22
    csuc
    #
    cA
    wss
    #
    @24
    @41
    @34
    @22
    csn
    #
    cA
    wss
    #
    @46
    @36
    @22
    cA
    snssi
    @34
    @48
    wa
    @22
    @47
    cun
    #
    cA
    wss
    @46
    @22
    @47
    cA
    unss
    @45
    @49
    cA
    @22
    df-suc
    sseq1i
    sylbb2
    sylancr
    @41
    @46
    @45
    @21
    wcel
    #
    @24
    @46
    @41
    @50
    @46
    @45
    wtr
    #
    @18
    vt
    @45
    wral
    #
    @41
    @50
    wi
    @38
    @51
    @39
    @22
    suctr
    ax-mp
    @10
    vz
    @22
    wral
    #
    @52
    @53
    @28
    vx
    @21
    vz
    vx
    @21
    untuni
    @33
    mprgbir
    #
    vz
    vt
    @22
    vt
    @21
    @20
    vt
    vw
    @15
    @16
    @19
    vt
    @15
    vt
    nfv
    @16
    vt
    nfv
    @18
    vt
    @14
    nfra1
    nf3an
    nfab
    nfuni
    #
    untsucf
    ax-mp
    @45
    cvv
    wcel
    #
    @46
    @51
    @52
    w3a
    #
    @50
    @41
    @56
    @50
    @57
    @25
    cA
    wss
    #
    @25
    wtr
    #
    @18
    vt
    @25
    wral
    #
    w3a
    #
    @57
    vz
    @45
    @21
    cvv
    @25
    @45
    wceq
    @58
    @46
    @59
    @51
    @60
    @52
    @25
    @45
    cA
    sseq1
    @25
    @45
    treq
    @18
    vt
    @25
    @45
    vt
    @25
    nfcv
    vt
    @22
    @55
    nfsuc
    raleqf
    3anbi123d
    @20
    @61
    vw
    vz
    @14
    @25
    wceq
    @15
    @58
    @16
    @59
    @19
    @60
    @14
    @25
    cA
    sseq1
    @14
    @25
    treq
    @18
    vt
    @14
    @25
    raleq
    3anbi123d
    cbvabv
    elab2g
    biimprd
    @22
    cA
    sucexg
    syl11
    mp3an23
    com12
    @50
    @45
    @22
    wss
    @41
    @24
    @45
    @21
    elssuni
    @22
    @22
    cA
    sucssel
    syl5
    syld
    mpd
    syl6
    mpan2i
    syl5bir
    mpani
    mt3i
    @23
    @38
    @53
    wa
    @12
    @38
    @53
    @39
    @54
    pm3.2i
    @23
    @38
    @8
    @53
    @11
    @22
    cA
    treq
    @10
    vz
    @22
    cA
    raleq
    anbi12d
    mpbii
    syl
    ex
end
