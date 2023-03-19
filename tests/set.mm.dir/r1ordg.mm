include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "con0.mm"
include "csuc.mm"
include "wss.mm"
include "simpl.mm"
include "word.mm"
include "wlim.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordsson.mm"
include "sseli.mm"
include "syl.mm"
include "onelon.mm"
include "sylan.mm"
include "suceloni.mm"
include "wi.mm"
include "eloni.mm"
include "ordsucss.mm"
include "imp.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "cpw.mm"
include "fvex.mm"
include "pwid.mm"
include "wb.mm"
include "limsuc.mm"
include "r1sucg.mm"
include "sylbir.mm"
include "syl5eleqr.mm"
include "a1i.mm"
include "wtr.mm"
include "r1tr.mm"
include "dftr4.mm"
include "mpbi.mm"
include "syl5sseqr.mm"
include "sseld.mm"
include "a2i.mm"
include "syl5bir.mm"
include "wral.mm"
include "ciun.mm"
include "wrex.mm"
include "simprl.mm"
include "simplr.mm"
include "sucelon.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "ordelsuc.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "mpbid.mm"
include "simprr.mm"
include "ordtr1.mm"
include "rspcev.mm"
include "eliun.mm"
include "simpll.mm"
include "r1limg.mm"
include "eleqtrrd.mm"
include "expr.mm"
include "a1d.mm"
include "tfindsg.mm"
include "impr.mm"
include "syl22anc.mm"
include "ex.mm"

theorem r1ordg
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. dom R1 -> ( A e. B -> ( R1 ` A ) e. ( R1 ` B ) ) )

  proof
    cB
    cr1
    cdm
    #
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cr1
    cfv
    #
    cB
    cr1
    cfv
    #
    wcel
    #
    @1
    @2
    wa
    #
    cB
    con0
    wcel
    #
    cA
    csuc
    #
    con0
    wcel
    #
    @8
    cB
    wss
    #
    @1
    @5
    @6
    @1
    @7
    @1
    @2
    simpl
    #
    @0
    con0
    cB
    @0
    word
    #
    @0
    con0
    wss
    @0
    wlim
    #
    @12
    cr1
    wfun
    @13
    r1funlim
    simpri
    #
    @0
    limord
    ax-mp
    #
    @0
    ordsson
    ax-mp
    sseli
    #
    syl
    @6
    cA
    con0
    wcel
    #
    @9
    @1
    @7
    @2
    @17
    @16
    cB
    cA
    onelon
    sylan
    cA
    suceloni
    syl
    @1
    @7
    @2
    @10
    @16
    @7
    @2
    @10
    @7
    cB
    word
    @2
    @10
    wi
    cB
    eloni
    cA
    cB
    ordsucss
    syl
    imp
    sylan
    @11
    @7
    @9
    wa
    @10
    @1
    @5
    vx
    cv
    #
    @0
    wcel
    #
    @3
    @18
    cr1
    cfv
    #
    wcel
    #
    wi
    #
    @8
    @0
    wcel
    #
    @3
    @8
    cr1
    cfv
    #
    wcel
    #
    wi
    #
    vy
    cv
    #
    @0
    wcel
    #
    @3
    @27
    cr1
    cfv
    #
    wcel
    #
    wi
    #
    @27
    csuc
    #
    @0
    wcel
    #
    @3
    @32
    cr1
    cfv
    #
    wcel
    #
    wi
    #
    @1
    @5
    wi
    vx
    vy
    cB
    @8
    @18
    @8
    wceq
    #
    @19
    @23
    @21
    @25
    @18
    @8
    @0
    eleq1
    @37
    @20
    @24
    @3
    @18
    @8
    cr1
    fveq2
    eleq2d
    imbi12d
    @18
    @27
    wceq
    #
    @19
    @28
    @21
    @30
    @18
    @27
    @0
    eleq1
    @38
    @20
    @29
    @3
    @18
    @27
    cr1
    fveq2
    eleq2d
    imbi12d
    @18
    @32
    wceq
    #
    @19
    @33
    @21
    @35
    @18
    @32
    @0
    eleq1
    @39
    @20
    @34
    @3
    @18
    @32
    cr1
    fveq2
    eleq2d
    imbi12d
    @18
    cB
    wceq
    #
    @19
    @1
    @21
    @5
    @18
    cB
    @0
    eleq1
    @40
    @20
    @4
    @3
    @18
    cB
    cr1
    fveq2
    eleq2d
    imbi12d
    @26
    @9
    @23
    @3
    @3
    cpw
    #
    @24
    @3
    cA
    cr1
    fvex
    pwid
    #
    @23
    cA
    @0
    wcel
    #
    @24
    @41
    wceq
    #
    @13
    @43
    @23
    wb
    @14
    @0
    cA
    limsuc
    ax-mp
    cA
    r1sucg
    #
    sylbir
    syl5eleqr
    a1i
    @31
    @36
    wi
    @27
    con0
    wcel
    @9
    wa
    @8
    @27
    wss
    #
    wa
    @33
    @28
    @31
    @35
    @13
    @28
    @33
    wb
    @14
    @0
    @27
    limsuc
    ax-mp
    @28
    @30
    @35
    @28
    @29
    @34
    @3
    @28
    @29
    cpw
    #
    @29
    @34
    @29
    wtr
    @29
    @47
    wss
    @27
    r1tr
    @29
    dftr4
    mpbi
    @27
    r1sucg
    syl5sseqr
    sseld
    a2i
    syl5bir
    a1i
    @18
    wlim
    #
    @9
    wa
    #
    @8
    @18
    wss
    #
    wa
    @22
    @46
    @31
    wi
    vy
    @18
    wral
    @49
    @50
    @19
    @21
    @49
    @50
    @19
    wa
    #
    wa
    #
    @3
    vy
    @18
    @29
    ciun
    #
    @20
    @52
    @30
    vy
    @18
    wrex
    #
    @3
    @53
    wcel
    @52
    @8
    @18
    wcel
    #
    @25
    @54
    @52
    cA
    @18
    wcel
    #
    @55
    @52
    @56
    @50
    @49
    @50
    @19
    simprl
    @52
    @17
    @18
    word
    #
    @56
    @50
    wb
    @52
    @9
    @17
    @48
    @9
    @51
    simplr
    cA
    sucelon
    sylibr
    @48
    @57
    @9
    @51
    @18
    limord
    ad2antrr
    cA
    @18
    con0
    ordelsuc
    syl2anc
    mpbird
    #
    @48
    @56
    @55
    wb
    @9
    @51
    @18
    cA
    limsuc
    ad2antrr
    mpbid
    @52
    @3
    @41
    @24
    @42
    @52
    @43
    @44
    @52
    @56
    @19
    @43
    @58
    @49
    @50
    @19
    simprr
    #
    @12
    @56
    @19
    wa
    @43
    wi
    @15
    cA
    @18
    @0
    ordtr1
    ax-mp
    syl2anc
    @45
    syl
    syl5eleqr
    @30
    @25
    vy
    @8
    @18
    @27
    @8
    wceq
    @29
    @24
    @3
    @27
    @8
    cr1
    fveq2
    eleq2d
    rspcev
    syl2anc
    vy
    @3
    @18
    @29
    eliun
    sylibr
    @52
    @19
    @48
    @20
    @53
    wceq
    @59
    @48
    @9
    @51
    simpll
    vy
    @18
    r1limg
    syl2anc
    eleqtrrd
    expr
    a1d
    tfindsg
    impr
    syl22anc
    ex
end
