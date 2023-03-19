include "wss.mm"
include "wtr.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "com.mm"
include "cfv.mm"
include "ciun.mm"
include "wrex.mm"
include "c0.mm"
include "wcel.mm"
include "peano1.mm"
include "cvv.mm"
include "cuni.mm"
include "cun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "fveq1i.mm"
include "wceq.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "eqtr2i.mm"
include "eqimssi.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "ssiun.mm"
include "sseqtr4i.mm"
include "dftr2.mm"
include "csuc.mm"
include "eliun.mm"
include "anbi2i.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "elunii.mm"
include "ssun2.mm"
include "fvex.mm"
include "uniex.mm"
include "unex.mm"
include "weq.mm"
include "id.mm"
include "unieq.mm"
include "uneq12d.mm"
include "frsucmpt2.mm"
include "mpan2.mm"
include "syl5sseqr.mm"
include "sseld.mm"
include "syl5.mm"
include "reximia.mm"
include "sylbi.mm"
include "peano2.mm"
include "eleq2d.mm"
include "ex.mm"
include "syl.mm"
include "rexlimiv.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "ax-gen.mm"
include "mpgbir.mm"
include "wb.mm"
include "treq.mm"
include "mpbir.mm"
include "wral.mm"
include "sseq1d.mm"
include "eqtri.mm"
include "sseq1i.mm"
include "biimpri.mm"
include "adantr.mm"
include "uniss.mm"
include "df-tr.mm"
include "sstr2.mm"
include "syl5bi.mm"
include "anc2li.mm"
include "unss.mm"
include "syl6ib.mm"
include "biimprd.mm"
include "syl9r.mm"
include "com23.mm"
include "adantld.mm"
include "finds2.mm"
include "com12.mm"
include "ralrimiv.mm"
include "cbviunv.mm"
include "iunss.mm"
include "bitri.mm"
include "3pm3.2i.mm"

theorem trcl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cF: class F
  let vv: setvar v
  let vu: setvar u
  assume trcl.1: |- A e. _V
  assume trcl.2: |- F = ( rec ( ( z e. _V |-> ( z u. U. z ) ) , A ) |` _om )
  assume trcl.3: |- C = U_ y e. _om ( F ` y )

  disjoint x z
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint F v
  assert |- ( A C_ C /\ Tr C /\ A. x ( ( A C_ x /\ Tr x ) -> C C_ x ) )

  proof
    cA
    cC
    wss
    cC
    wtr
    #
    cA
    vx
    cv
    #
    wss
    #
    @1
    wtr
    #
    wa
    #
    cC
    @1
    wss
    #
    wi
    #
    vx
    wal
    cA
    vy
    com
    vy
    cv
    #
    cF
    cfv
    #
    ciun
    #
    cC
    cA
    @8
    wss
    #
    vy
    com
    wrex
    #
    cA
    @9
    wss
    c0
    com
    wcel
    cA
    c0
    cF
    cfv
    #
    wss
    #
    @11
    peano1
    cA
    @12
    @12
    c0
    vz
    cvv
    vz
    cv
    #
    @14
    cuni
    #
    cun
    #
    cmpt
    #
    cA
    crdg
    com
    cres
    #
    cfv
    #
    cA
    c0
    cF
    @18
    trcl.2
    fveq1i
    #
    cA
    cvv
    wcel
    @19
    cA
    wceq
    trcl.1
    cA
    cvv
    @17
    fr0g
    ax-mp
    #
    eqtr2i
    eqimssi
    @10
    @13
    vy
    c0
    com
    @7
    c0
    wceq
    @8
    @12
    cA
    @7
    c0
    cF
    fveq2
    sseq2d
    rspcev
    mp2an
    vy
    com
    @8
    cA
    ssiun
    ax-mp
    trcl.3
    sseqtr4i
    @0
    @9
    wtr
    #
    @22
    vv
    cv
    #
    vu
    cv
    #
    wcel
    #
    @24
    @9
    wcel
    #
    wa
    #
    @23
    @9
    wcel
    #
    wi
    #
    vu
    wal
    vv
    vv
    vu
    @9
    dftr2
    @29
    vu
    @27
    @23
    @7
    csuc
    #
    cF
    cfv
    #
    wcel
    #
    vy
    com
    wrex
    #
    @28
    @27
    @25
    @24
    @8
    wcel
    #
    wa
    #
    vy
    com
    wrex
    #
    @33
    @27
    @25
    @34
    vy
    com
    wrex
    #
    wa
    @36
    @26
    @37
    @25
    vy
    @24
    com
    @8
    eliun
    anbi2i
    @25
    @34
    vy
    com
    r19.42v
    bitr4i
    @35
    @32
    vy
    com
    @35
    @23
    @8
    cuni
    #
    wcel
    @7
    com
    wcel
    #
    @32
    @23
    @24
    @8
    elunii
    @39
    @38
    @31
    @23
    @39
    @8
    @38
    cun
    #
    @38
    @31
    @38
    @8
    ssun2
    @39
    @40
    cvv
    wcel
    @31
    @40
    wceq
    @8
    @38
    @7
    cF
    fvex
    #
    @8
    @41
    uniex
    unex
    vz
    vx
    cA
    @7
    @16
    @40
    @1
    @1
    cuni
    #
    cun
    cF
    cvv
    trcl.2
    vx
    vz
    weq
    #
    @1
    @14
    @42
    @15
    @43
    id
    @1
    @14
    unieq
    uneq12d
    @1
    @8
    wceq
    #
    @1
    @8
    @42
    @38
    @44
    id
    @1
    @8
    unieq
    uneq12d
    frsucmpt2
    mpan2
    #
    syl5sseqr
    sseld
    syl5
    reximia
    sylbi
    @33
    @23
    @8
    wcel
    #
    vy
    com
    wrex
    #
    @28
    @33
    @23
    @24
    cF
    cfv
    #
    wcel
    #
    vu
    com
    wrex
    #
    @47
    @32
    @50
    vy
    com
    @39
    @30
    com
    wcel
    #
    @32
    @50
    wi
    @7
    peano2
    @51
    @32
    @50
    @49
    @32
    vu
    @30
    com
    @24
    @30
    wceq
    @48
    @31
    @23
    @24
    @30
    cF
    fveq2
    eleq2d
    rspcev
    ex
    syl
    rexlimiv
    @46
    @49
    vy
    vu
    com
    vy
    vu
    weq
    @8
    @48
    @23
    @7
    @24
    cF
    fveq2
    eleq2d
    cbvrexv
    sylibr
    vy
    @23
    com
    @8
    eliun
    sylibr
    syl
    ax-gen
    mpgbir
    cC
    @9
    wceq
    @0
    @22
    wb
    trcl.3
    cC
    @9
    treq
    ax-mp
    mpbir
    @6
    vx
    @4
    @23
    cF
    cfv
    #
    @1
    wss
    #
    vv
    com
    wral
    #
    @5
    @4
    @53
    vv
    com
    @23
    com
    wcel
    @4
    @53
    @53
    @12
    @1
    wss
    #
    @8
    @1
    wss
    #
    @31
    @1
    wss
    #
    @4
    vv
    vy
    @23
    c0
    wceq
    @52
    @12
    @1
    @23
    c0
    cF
    fveq2
    sseq1d
    vv
    vy
    weq
    @52
    @8
    @1
    @23
    @7
    cF
    fveq2
    sseq1d
    @23
    @30
    wceq
    @52
    @31
    @1
    @23
    @30
    cF
    fveq2
    sseq1d
    @2
    @55
    @3
    @55
    @2
    @12
    cA
    @1
    @12
    @19
    cA
    @20
    @21
    eqtri
    sseq1i
    biimpri
    adantr
    @39
    @3
    @56
    @57
    wi
    @2
    @39
    @56
    @3
    @57
    @56
    @3
    @40
    @1
    wss
    #
    @39
    @57
    @56
    @3
    @56
    @38
    @1
    wss
    #
    wa
    @58
    @56
    @3
    @59
    @56
    @38
    @42
    wss
    #
    @3
    @59
    wi
    @8
    @1
    uniss
    @3
    @42
    @1
    wss
    @60
    @59
    @1
    df-tr
    @38
    @42
    @1
    sstr2
    syl5bi
    syl
    anc2li
    @8
    @38
    @1
    unss
    syl6ib
    @39
    @57
    @58
    @39
    @31
    @40
    @1
    @45
    sseq1d
    biimprd
    syl9r
    com23
    adantld
    finds2
    com12
    ralrimiv
    @5
    vv
    com
    @52
    ciun
    #
    @1
    wss
    @54
    cC
    @61
    @1
    cC
    @9
    @61
    trcl.3
    vy
    vv
    com
    @8
    @52
    @7
    @23
    cF
    fveq2
    cbviunv
    eqtri
    sseq1i
    vv
    com
    @52
    @1
    iunss
    bitri
    sylibr
    ax-gen
    3pm3.2i
end
