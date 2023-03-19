include "com.mm"
include "cima.mm"
include "wfn.mm"
include "cvv.mm"
include "wf.mm"
include "cres.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wral.mm"
include "cfv.mm"
include "wcel.mm"
include "csuc.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "c0.mm"
include "cid.mm"
include "crdg.mm"
include "frfnom.mm"
include "reseq1i.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "c2nd.mm"
include "fvres.mm"
include "seqomlem1.mm"
include "eqtrd.mm"
include "fvex.mm"
include "opelxpi.mm"
include "mpan2.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "frn.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wrex.mm"
include "df-br.mm"
include "fvelrnb.mm"
include "eqeq1d.mm"
include "rexbiia.mm"
include "3bitri.mm"
include "wa.mm"
include "adantl.mm"
include "vex.mm"
include "opth1.mm"
include "syl6bi.mm"
include "fveq2.mm"
include "biimpd.mm"
include "syli.mm"
include "op2nd.mm"
include "syl6req.mm"
include "syl6.mm"
include "rexlimdva.mm"
include "rspcev.mm"
include "mpdan.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "syl5bb.mm"
include "alrimiv.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "spcev.mm"
include "syl.mm"
include "df-eu.mm"
include "sylibr.mm"
include "dff3.mm"
include "df-ima.mm"
include "feq1i.mm"
include "dffn2.mm"

theorem seqomlem2
  let vv: setvar v
  let cQ: class Q
  let vi: setvar i
  let cF: class F
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  assume seqomlem.a: |- Q = rec ( ( i e. _om , v e. _V |-> <. suc i , ( i F v ) >. ) , <. (/) , ( _I ` I ) >. )

  disjoint Q i
  disjoint Q v
  disjoint i v
  disjoint F i
  disjoint F v
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint a b
  disjoint a c
  disjoint a i
  disjoint a v
  disjoint b c
  disjoint b i
  disjoint b v
  disjoint c i
  disjoint c v
  disjoint A a
  disjoint A b
  disjoint A i
  disjoint A v
  disjoint F a
  disjoint F b
  disjoint I a
  disjoint I b
  assert |- ( Q " _om ) Fn _om

  proof
    cQ
    com
    cima
    #
    com
    wfn
    com
    cvv
    @0
    wf
    #
    @1
    com
    cvv
    cQ
    com
    cres
    #
    crn
    #
    wf
    #
    @4
    @3
    com
    cvv
    cxp
    #
    wss
    #
    va
    cv
    #
    vb
    cv
    #
    @3
    wbr
    #
    vb
    weu
    #
    va
    com
    wral
    com
    @5
    @2
    wf
    #
    @6
    @11
    @2
    com
    wfn
    #
    @8
    @2
    cfv
    #
    @5
    wcel
    #
    vb
    com
    wral
    @12
    vi
    vv
    com
    cvv
    vi
    cv
    #
    csuc
    @15
    vv
    cv
    cF
    co
    cop
    cmpt2
    #
    c0
    cI
    cid
    cfv
    cop
    #
    crdg
    #
    com
    cres
    #
    com
    wfn
    @17
    @16
    frfnom
    com
    @2
    @19
    cQ
    @18
    com
    seqomlem.a
    reseq1i
    fneq1i
    mpbir
    #
    @14
    vb
    com
    @8
    com
    wcel
    #
    @13
    @8
    @8
    cQ
    cfv
    #
    c2nd
    cfv
    #
    cop
    #
    @5
    @21
    @13
    @22
    @24
    @8
    com
    cQ
    fvres
    vv
    @8
    cQ
    vi
    cF
    cI
    seqomlem.a
    seqomlem1
    eqtrd
    @21
    @23
    cvv
    wcel
    @24
    @5
    wcel
    @22
    c2nd
    fvex
    @8
    @23
    com
    cvv
    opelxpi
    mpan2
    eqeltrd
    rgen
    vb
    com
    @5
    @2
    ffnfv
    mpbir2an
    com
    @5
    @2
    frn
    ax-mp
    @10
    va
    com
    @7
    com
    wcel
    #
    @9
    @8
    vc
    cv
    #
    wceq
    #
    wb
    #
    vb
    wal
    #
    vc
    wex
    #
    @10
    @25
    @9
    @8
    @7
    cQ
    cfv
    #
    c2nd
    cfv
    #
    wceq
    #
    wb
    #
    vb
    wal
    #
    @30
    @25
    @34
    vb
    @9
    @26
    cQ
    cfv
    #
    @7
    @8
    cop
    #
    wceq
    #
    vc
    com
    wrex
    #
    @25
    @33
    @9
    @37
    @3
    wcel
    #
    @26
    @2
    cfv
    #
    @37
    wceq
    #
    vc
    com
    wrex
    #
    @39
    @7
    @8
    @3
    df-br
    @12
    @40
    @43
    wb
    @20
    vc
    com
    @37
    @2
    fvelrnb
    ax-mp
    @42
    @38
    vc
    com
    @26
    com
    wcel
    #
    @41
    @36
    @37
    @26
    com
    cQ
    fvres
    eqeq1d
    rexbiia
    3bitri
    @25
    @39
    @33
    @25
    @38
    @33
    vc
    com
    @25
    @44
    wa
    #
    @38
    @31
    @37
    wceq
    #
    @33
    @38
    @45
    @26
    @7
    wceq
    #
    @46
    @45
    @38
    @26
    @36
    c2nd
    cfv
    #
    cop
    #
    @37
    wceq
    @47
    @45
    @36
    @49
    @37
    @44
    @36
    @49
    wceq
    @25
    vv
    @26
    cQ
    vi
    cF
    cI
    seqomlem.a
    seqomlem1
    adantl
    eqeq1d
    @26
    @48
    @7
    @8
    vc
    vex
    @36
    c2nd
    fvex
    opth1
    syl6bi
    @47
    @38
    @46
    @47
    @36
    @31
    @37
    @26
    @7
    cQ
    fveq2
    #
    eqeq1d
    biimpd
    syli
    @46
    @32
    @37
    c2nd
    cfv
    @8
    @31
    @37
    c2nd
    fveq2
    @7
    @8
    va
    vex
    vb
    vex
    op2nd
    syl6req
    syl6
    rexlimdva
    @25
    @39
    @33
    @36
    @7
    @32
    cop
    #
    wceq
    #
    vc
    com
    wrex
    #
    @25
    @31
    @51
    wceq
    #
    @53
    vv
    @7
    cQ
    vi
    cF
    cI
    seqomlem.a
    seqomlem1
    @52
    @54
    vc
    @7
    com
    @47
    @36
    @31
    @51
    @50
    eqeq1d
    rspcev
    mpdan
    @33
    @38
    @52
    vc
    com
    @33
    @37
    @51
    @36
    @8
    @32
    @7
    opeq2
    eqeq2d
    rexbidv
    syl5ibrcom
    impbid
    syl5bb
    alrimiv
    @29
    @35
    vc
    @32
    @31
    c2nd
    fvex
    @26
    @32
    wceq
    #
    @28
    @34
    vb
    @55
    @27
    @33
    @9
    @26
    @32
    @8
    eqeq2
    bibi2d
    albidv
    spcev
    syl
    @9
    vb
    vc
    df-eu
    sylibr
    rgen
    va
    vb
    com
    cvv
    @3
    dff3
    mpbir2an
    com
    cvv
    @0
    @3
    cQ
    com
    df-ima
    feq1i
    mpbir
    com
    @0
    dffn2
    mpbir
end
