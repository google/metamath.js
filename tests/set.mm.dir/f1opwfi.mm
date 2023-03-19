include "wf1o.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cima.mm"
include "ccnv.mm"
include "cmpt.mm"
include "eqid.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl.mm"
include "syl5sseq.mm"
include "adantr.mm"
include "wb.mm"
include "cres.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ofun.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwi.mm"
include "adantl.mm"
include "f1odm.mm"
include "sseqtr4d.mm"
include "fores.mm"
include "syl2anc.mm"
include "fofi.mm"
include "elpwg.mm"
include "mpbird.mm"
include "elind.mm"
include "dfdm4.mm"
include "syl5eqr.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "f1ocnv.mm"
include "anim12i.mm"
include "foimacnv.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1imacnv.mm"
include "impbid.mm"
include "sylan2.mm"
include "f1o2d.mm"

theorem f1opwfi
  let cA: class A
  let cB: class B
  let cF: class F
  let vb: setvar b
  let va: setvar a

  disjoint A b
  disjoint B b
  disjoint F b
  disjoint a b
  disjoint A a
  disjoint B a
  disjoint F a
  assert |- ( F : A -1-1-onto-> B -> ( b e. ( ~P A i^i Fin ) |-> ( F " b ) ) : ( ~P A i^i Fin ) -1-1-onto-> ( ~P B i^i Fin ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    vb
    va
    cA
    cpw
    #
    cfn
    cin
    #
    cB
    cpw
    #
    cfn
    cin
    #
    cF
    vb
    cv
    #
    cima
    #
    cF
    ccnv
    #
    va
    cv
    #
    cima
    #
    vb
    @2
    @6
    cmpt
    #
    @10
    eqid
    @0
    @5
    @2
    wcel
    #
    wa
    #
    @3
    cfn
    @6
    @12
    @6
    @3
    wcel
    #
    @6
    cB
    wss
    #
    @0
    @14
    @11
    @0
    cF
    crn
    #
    @6
    cB
    cF
    @5
    imassrn
    @0
    cA
    cB
    cF
    wfo
    #
    @15
    cB
    wceq
    cA
    cB
    cF
    f1ofo
    #
    cA
    cB
    cF
    forn
    syl
    syl5sseq
    adantr
    @12
    @6
    cfn
    wcel
    #
    @13
    @14
    wb
    @12
    @5
    cfn
    wcel
    @5
    @6
    cF
    @5
    cres
    #
    wfo
    #
    @18
    @12
    @2
    cfn
    @5
    @1
    cfn
    inss2
    @0
    @11
    simpr
    sseldi
    @12
    cF
    wfun
    #
    @5
    cF
    cdm
    #
    wss
    @20
    @0
    @21
    @11
    cA
    cB
    cF
    f1ofun
    adantr
    @12
    @5
    cA
    @22
    @11
    @5
    cA
    wss
    #
    @0
    @11
    @5
    @1
    wcel
    #
    @23
    @2
    @1
    @5
    @1
    cfn
    inss1
    sseli
    #
    @5
    cA
    elpwi
    #
    syl
    adantl
    @0
    @22
    cA
    wceq
    @11
    cA
    cB
    cF
    f1odm
    #
    adantr
    sseqtr4d
    @5
    cF
    fores
    syl2anc
    @5
    @6
    @19
    fofi
    syl2anc
    #
    @6
    cB
    cfn
    elpwg
    syl
    mpbird
    @28
    elind
    @0
    @8
    @4
    wcel
    #
    wa
    #
    @1
    cfn
    @9
    @30
    @9
    @1
    wcel
    #
    @9
    cA
    wss
    #
    @0
    @32
    @29
    @0
    @7
    crn
    #
    @9
    cA
    @7
    @8
    imassrn
    @0
    @33
    @22
    cA
    cF
    dfdm4
    @27
    syl5eqr
    syl5sseq
    adantr
    @30
    @9
    cfn
    wcel
    #
    @31
    @32
    wb
    @30
    @8
    cfn
    wcel
    @8
    @9
    @7
    @8
    cres
    #
    wfo
    #
    @34
    @30
    @4
    cfn
    @8
    @3
    cfn
    inss2
    @0
    @29
    simpr
    sseldi
    @30
    @7
    wfun
    #
    @8
    @7
    cdm
    #
    wss
    @36
    @0
    @37
    @29
    @0
    @16
    @37
    cA
    cB
    cF
    dff1o3
    simprbi
    adantr
    @30
    @8
    cB
    @38
    @30
    @8
    @3
    wcel
    #
    @8
    cB
    wss
    #
    @29
    @39
    @0
    @4
    @3
    @8
    @3
    cfn
    inss1
    sseli
    #
    adantl
    @8
    cB
    elpwi
    #
    syl
    @30
    cB
    cA
    @7
    wf1o
    #
    @38
    cB
    wceq
    @0
    @43
    @29
    cA
    cB
    cF
    f1ocnv
    adantr
    cB
    cA
    @7
    f1odm
    syl
    sseqtr4d
    @8
    @7
    fores
    syl2anc
    @8
    @9
    @35
    fofi
    syl2anc
    #
    @9
    cA
    cfn
    elpwg
    syl
    mpbird
    @44
    elind
    @11
    @29
    wa
    @0
    @24
    @39
    wa
    #
    @5
    @9
    wceq
    #
    @8
    @6
    wceq
    #
    wb
    @11
    @24
    @29
    @39
    @25
    @41
    anim12i
    @0
    @45
    wa
    #
    @46
    @47
    @48
    @47
    @46
    @8
    cF
    @9
    cima
    #
    wceq
    @48
    @49
    @8
    @0
    @16
    @40
    @49
    @8
    wceq
    @45
    @17
    @39
    @40
    @24
    @42
    adantl
    cA
    cB
    @8
    cF
    foimacnv
    syl2an
    eqcomd
    @46
    @6
    @49
    @8
    @5
    @9
    cF
    imaeq2
    eqeq2d
    syl5ibrcom
    @48
    @46
    @47
    @5
    @7
    @6
    cima
    #
    wceq
    @48
    @50
    @5
    @0
    cA
    cB
    cF
    wf1
    @23
    @50
    @5
    wceq
    @45
    cA
    cB
    cF
    f1of1
    @24
    @23
    @39
    @26
    adantr
    cA
    cB
    @5
    cF
    f1imacnv
    syl2an
    eqcomd
    @47
    @9
    @50
    @5
    @8
    @6
    @7
    imaeq2
    eqeq2d
    syl5ibrcom
    impbid
    sylan2
    f1o2d
end
