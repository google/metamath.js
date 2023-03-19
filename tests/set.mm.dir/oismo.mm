include "con0.mm"
include "wss.mm"
include "wsmo.mm"
include "crn.mm"
include "wceq.mm"
include "cdm.mm"
include "wfo.mm"
include "wa.mm"
include "cep.mm"
include "wiso.mm"
include "wwe.mm"
include "wse.mm"
include "epweon.mm"
include "wess.mm"
include "mpi.mm"
include "epse.mm"
include "oiiso2.mm"
include "sylancl.mm"
include "word.mm"
include "wb.mm"
include "oicl.mm"
include "wf.mm"
include "oif.mm"
include "frn.mm"
include "ax-mp.mm"
include "id.mm"
include "syl5ss.mm"
include "smoiso2.mm"
include "sylancr.mm"
include "mpbird.mm"
include "simprd.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "simprl.mm"
include "wf1o.mm"
include "cvv.mm"
include "adantr.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "ffn.mm"
include "mp1i.mm"
include "wbr.mm"
include "simplrr.mm"
include "wo.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "oiiniseg.mm"
include "syl22anc.mm"
include "ord.mm"
include "mt3d.mm"
include "vex.mm"
include "epelc.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "smogt.mm"
include "syl3anc.mm"
include "wi.mm"
include "ordelon.mm"
include "simpll.mm"
include "sseldd.mm"
include "ontr2.mm"
include "syl2anc.mm"
include "mp2and.mm"
include "ex.mm"
include "ssrdv.mm"
include "ssexd.mm"
include "fex2.mm"
include "ordtype2.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "4syl.mm"
include "eleqtrrd.mm"
include "expr.mm"
include "pm2.18d.mm"
include "eqssd.mm"
include "jca.mm"

theorem oismo
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume oismo.1: |- F = OrdIso ( _E , A )


  assert |- ( A C_ On -> ( Smo F /\ ran F = A ) )

  proof
    cA
    con0
    wss
    #
    cF
    wsmo
    #
    cF
    crn
    #
    cA
    wceq
    #
    @0
    cF
    cdm
    #
    @2
    cF
    wfo
    #
    @1
    @0
    @5
    @1
    wa
    #
    @4
    @2
    cep
    cep
    cF
    wiso
    #
    @0
    cA
    cep
    wwe
    #
    cA
    cep
    wse
    #
    @7
    @0
    con0
    cep
    wwe
    @8
    epweon
    cA
    con0
    cep
    wess
    mpi
    #
    cA
    epse
    #
    cA
    cep
    cF
    oismo.1
    oiiso2
    sylancl
    @0
    @4
    word
    #
    @2
    con0
    wss
    @6
    @7
    wb
    cA
    cep
    cF
    oismo.1
    oicl
    #
    @0
    @2
    cA
    con0
    @4
    cA
    cF
    wf
    #
    @2
    cA
    wss
    #
    cA
    cep
    cF
    oismo.1
    oif
    #
    @4
    cA
    cF
    frn
    ax-mp
    #
    @0
    id
    syl5ss
    @4
    @2
    cF
    smoiso2
    sylancr
    mpbird
    simprd
    #
    @0
    @2
    cA
    @15
    @0
    @17
    a1i
    @0
    vx
    cA
    @2
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @19
    @2
    wcel
    #
    @0
    @20
    wa
    @21
    @0
    @20
    @21
    wn
    #
    @21
    @0
    @20
    @22
    wa
    #
    wa
    #
    @19
    cA
    @2
    @0
    @20
    @22
    simprl
    #
    @24
    @4
    cA
    cep
    cep
    cF
    wiso
    #
    @4
    cA
    cF
    wf1o
    @4
    cA
    cF
    wfo
    @3
    @24
    @8
    @9
    cF
    cvv
    wcel
    #
    @26
    @0
    @8
    @23
    @10
    adantr
    @9
    @24
    @11
    a1i
    @24
    @4
    @19
    cF
    wf
    #
    @4
    cvv
    wcel
    @20
    @27
    @24
    cF
    @4
    wfn
    #
    vy
    cv
    #
    cF
    cfv
    #
    @19
    wcel
    #
    vy
    @4
    wral
    @28
    @14
    @29
    @24
    @16
    @4
    cA
    cF
    ffn
    #
    mp1i
    @24
    @32
    vy
    @4
    @24
    @30
    @4
    wcel
    #
    wa
    #
    @31
    @19
    cep
    wbr
    #
    @32
    @35
    @36
    @21
    @0
    @20
    @22
    @34
    simplrr
    @35
    @36
    @21
    @35
    @8
    @9
    @20
    @34
    @36
    @21
    wo
    @0
    @8
    @23
    @34
    @10
    ad2antrr
    @9
    @35
    @11
    a1i
    @0
    @20
    @22
    @34
    simplrl
    #
    @24
    @34
    simpr
    #
    cA
    cep
    cF
    @30
    @19
    oismo.1
    oiiniseg
    syl22anc
    ord
    mt3d
    @31
    @19
    vx
    vex
    epelc
    sylib
    #
    ralrimiva
    vy
    @4
    @19
    cF
    ffnfv
    sylanbrc
    @24
    @4
    @19
    cA
    @25
    @24
    vy
    @4
    @19
    @24
    @34
    @30
    @19
    wcel
    #
    @35
    @30
    @31
    wss
    #
    @32
    @40
    @35
    @29
    @1
    @34
    @41
    @14
    @29
    @35
    @16
    @33
    mp1i
    @0
    @1
    @23
    @34
    @18
    ad2antrr
    @38
    @4
    @30
    cF
    smogt
    syl3anc
    @39
    @35
    @30
    con0
    wcel
    #
    @19
    con0
    wcel
    @41
    @32
    wa
    @40
    wi
    @35
    @12
    @34
    @42
    @13
    @38
    @4
    @30
    ordelon
    sylancr
    @35
    cA
    con0
    @19
    @0
    @23
    @34
    simpll
    @37
    sseldd
    @30
    @31
    @19
    ontr2
    syl2anc
    mp2and
    ex
    ssrdv
    ssexd
    @25
    @4
    @19
    cF
    cvv
    cA
    fex2
    syl3anc
    cA
    cep
    cF
    oismo.1
    ordtype2
    syl3anc
    @4
    cA
    cep
    cep
    cF
    isof1o
    @4
    cA
    cF
    f1ofo
    @4
    cA
    cF
    forn
    4syl
    eleqtrrd
    expr
    pm2.18d
    ex
    ssrdv
    eqssd
    jca
end
