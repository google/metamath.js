include "wcel.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "c1o.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "cres.mm"
include "wf1o.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf1.mm"
include "wss.mm"
include "eqid.mm"
include "pw2f1o2.mm"
include "f1of1.mm"
include "syl.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "f1ores.mm"
include "sylancl.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "csupp.mm"
include "wfun.mm"
include "cvv.mm"
include "w3a.mm"
include "elmapfun.mm"
include "id.mm"
include "0ex.mm"
include "a1i.mm"
include "3jca.mm"
include "adantl.mm"
include "funisfsupp.mm"
include "cdif.mm"
include "wf.mm"
include "anim2i.mm"
include "elmapi.mm"
include "frnsuppeq.mm"
include "sylc.mm"
include "cun.mm"
include "csuc.mm"
include "df-2o.mm"
include "df-suc.mm"
include "equncomi.mm"
include "eqtri.mm"
include "df1o2.mm"
include "eqcomi.mm"
include "difeq12i.mm"
include "difun2.mm"
include "incom.mm"
include "word.mm"
include "1on.mm"
include "onordi.mm"
include "orddisj.mm"
include "ax-mp.mm"
include "disj3.mm"
include "mpbi.mm"
include "eqtr4i.mm"
include "imaeq2i.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "biantrurd.mm"
include "3bitrd.mm"
include "elfpw.mm"
include "syl6bbr.mm"
include "rabbidva.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "cbvmptv.mm"
include "mptpreima.mm"
include "3eqtr4g.mm"
include "imaeq2d.mm"
include "wfo.mm"
include "f1ofo.mm"
include "inss1.mm"
include "foimacnv.mm"
include "eqtrd.mm"
include "f1oeq3.mm"
include "resmpt.mm"
include "f1oeq1.mm"
include "mp1i.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem pwfi2f1o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cF: class F
  let cV: class V
  assume pwfi2f1o.s: |- S = { y e. ( 2o ^m A ) | y finSupp (/) }
  assume pwfi2f1o.f: |- F = ( x e. S |-> ( `' x " { 1o } ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint S x
  disjoint V x
  disjoint V y
  assert |- ( A e. V -> F : S -1-1-onto-> ( ~P A i^i Fin ) )

  proof
    cA
    cV
    wcel
    #
    cS
    vx
    c2o
    cA
    cmap
    co
    #
    vx
    cv
    #
    ccnv
    #
    c1o
    csn
    #
    cima
    #
    cmpt
    #
    cS
    cima
    #
    @6
    cS
    cres
    #
    wf1o
    #
    cS
    cA
    cpw
    #
    cfn
    cin
    #
    cF
    wf1o
    #
    @0
    @1
    @10
    @6
    wf1
    #
    cS
    @1
    wss
    #
    @9
    @0
    @1
    @10
    @6
    wf1o
    #
    @13
    vx
    cA
    @6
    cV
    @6
    eqid
    pw2f1o2
    #
    @1
    @10
    @6
    f1of1
    syl
    cS
    vy
    cv
    #
    c0
    cfsupp
    wbr
    #
    vy
    @1
    crab
    #
    @1
    pwfi2f1o.s
    @18
    vy
    @1
    ssrab2
    eqsstri
    #
    @1
    @10
    cS
    @6
    f1ores
    sylancl
    @0
    @9
    cS
    @11
    @8
    wf1o
    #
    @12
    @0
    @7
    @11
    wceq
    @9
    @21
    wb
    @0
    @7
    @6
    @6
    ccnv
    @11
    cima
    #
    cima
    #
    @11
    @0
    cS
    @22
    @6
    @0
    @19
    @17
    ccnv
    #
    @4
    cima
    #
    @11
    wcel
    #
    vy
    @1
    crab
    cS
    @22
    @0
    @18
    @26
    vy
    @1
    @0
    @17
    @1
    wcel
    #
    wa
    #
    @18
    @25
    cA
    wss
    #
    @25
    cfn
    wcel
    #
    wa
    #
    @26
    @28
    @18
    @17
    c0
    csupp
    co
    #
    cfn
    wcel
    #
    @30
    @31
    @28
    @17
    wfun
    #
    @27
    c0
    cvv
    wcel
    #
    w3a
    #
    @18
    @33
    wb
    @27
    @36
    @0
    @27
    @34
    @27
    @35
    @17
    c2o
    cA
    elmapfun
    @27
    id
    @35
    @27
    0ex
    a1i
    #
    3jca
    adantl
    @17
    @1
    cvv
    c0
    funisfsupp
    syl
    @28
    @32
    @25
    cfn
    @28
    @32
    @24
    c2o
    c0
    csn
    #
    cdif
    #
    cima
    #
    @25
    @28
    @0
    @35
    wa
    cA
    c2o
    @17
    wf
    #
    @32
    @40
    wceq
    @27
    @35
    @0
    @37
    anim2i
    @27
    @41
    @0
    @17
    c2o
    cA
    elmapi
    adantl
    #
    c2o
    @17
    cA
    cV
    cvv
    c0
    frnsuppeq
    sylc
    @39
    @4
    @24
    @39
    @4
    c1o
    cun
    #
    c1o
    cdif
    #
    @4
    c2o
    @43
    @38
    c1o
    c2o
    c1o
    csuc
    #
    @43
    df-2o
    @45
    c1o
    @4
    c1o
    df-suc
    equncomi
    eqtri
    c1o
    @38
    df1o2
    eqcomi
    difeq12i
    @44
    @4
    c1o
    cdif
    #
    @4
    @4
    c1o
    difun2
    @4
    c1o
    cin
    #
    c0
    wceq
    @4
    @46
    wceq
    @47
    c1o
    @4
    cin
    #
    c0
    @4
    c1o
    incom
    c1o
    word
    @48
    c0
    wceq
    c1o
    1on
    onordi
    c1o
    orddisj
    ax-mp
    eqtri
    @4
    c1o
    disj3
    mpbi
    eqtr4i
    eqtri
    imaeq2i
    syl6eq
    eleq1d
    @28
    @29
    @30
    @28
    @17
    cdm
    #
    @25
    cA
    @17
    @4
    cnvimass
    @28
    @41
    @49
    cA
    wceq
    @42
    cA
    c2o
    @17
    fdm
    syl
    syl5sseq
    biantrurd
    3bitrd
    @25
    cA
    elfpw
    syl6bbr
    rabbidva
    pwfi2f1o.s
    vy
    @1
    @25
    @11
    @6
    vx
    vy
    @1
    @5
    @25
    @2
    @17
    wceq
    @3
    @24
    @4
    @2
    @17
    cnveq
    imaeq1d
    cbvmptv
    mptpreima
    3eqtr4g
    imaeq2d
    @0
    @1
    @10
    @6
    wfo
    #
    @11
    @10
    wss
    @23
    @11
    wceq
    @0
    @15
    @50
    @16
    @1
    @10
    @6
    f1ofo
    syl
    @10
    cfn
    inss1
    @1
    @10
    @11
    @6
    foimacnv
    sylancl
    eqtrd
    @7
    @11
    cS
    @8
    f1oeq3
    syl
    @8
    cF
    wceq
    @21
    @12
    wb
    @0
    @8
    vx
    cS
    @5
    cmpt
    #
    cF
    @14
    @8
    @51
    wceq
    @20
    vx
    @1
    cS
    @5
    resmpt
    ax-mp
    pwfi2f1o.f
    eqtr4i
    cS
    @11
    @8
    cF
    f1oeq1
    mp1i
    bitrd
    mpbid
end
