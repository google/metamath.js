include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "wfn.mm"
include "ccnv.mm"
include "comu.mm"
include "co.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "coa.mm"
include "wral.mm"
include "csuc.mm"
include "wss.mm"
include "word.mm"
include "eloni.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "ordsucss.mm"
include "sylc.mm"
include "wi.mm"
include "onelon.mm"
include "ad2ant2lr.mm"
include "suceloni.mm"
include "syl.mm"
include "simplr.mm"
include "simpll.mm"
include "omwordi.mm"
include "syl3anc.mm"
include "mpd.mm"
include "simprr.mm"
include "wb.mm"
include "ad2ant2rl.mm"
include "omcl.mm"
include "syl2anc.mm"
include "oaord.mm"
include "mpbid.mm"
include "wceq.mm"
include "omsuc.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "ffn.mm"
include "cres.mm"
include "wbr.mm"
include "weu.mm"
include "cop.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "sylan.mm"
include "wn.mm"
include "noel.mm"
include "oveq1.mm"
include "om0r.mm"
include "sylan9eqr.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "ex.mm"
include "necon2ad.mm"
include "adantl.mm"
include "imp.mm"
include "omeu.mm"
include "vex.mm"
include "brcnv.mm"
include "wex.mm"
include "eleq1.mm"
include "biimpac.mm"
include "simplll.mm"
include "simpr.mm"
include "simplrr.mm"
include "oaword1.mm"
include "simplrl.mm"
include "ad2antrr.mm"
include "ontr2.mm"
include "mp2and.mm"
include "simpllr.mm"
include "ne0i.mm"
include "on0eln0.mm"
include "mpbird.mm"
include "om00el.mm"
include "simpld.mm"
include "omord2.mm"
include "syl31anc.mm"
include "impbid.mm"
include "expr.mm"
include "pm5.32rd.mm"
include "sylan2.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "an12.mm"
include "2exbidv.mm"
include "copab.mm"
include "cmpt2.mm"
include "coprab.mm"
include "df-mpt2.mm"
include "dfoprab2.mm"
include "3eqtri.mm"
include "breqi.mm"
include "df-br.mm"
include "opabid.mm"
include "3bitri.mm"
include "r2ex.mm"
include "3bitr4g.mm"
include "syl5bb.mm"
include "eubidv.mm"
include "ralrimiva.mm"
include "fnres.mm"
include "sylibr.mm"
include "wrel.mm"
include "cdm.mm"
include "relcnv.mm"
include "crn.mm"
include "df-rn.mm"
include "frn.mm"
include "syl5eqssr.mm"
include "relssres.mm"
include "sylancr.mm"
include "fneq1d.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem omxpenlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  assume omxpenlem.1: |- F = ( x e. B , y e. A |-> ( ( A .o x ) +o y ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A m
  disjoint A n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint B m
  disjoint B n
  disjoint F m
  disjoint F n
  assert |- ( ( A e. On /\ B e. On ) -> F : ( B X. A ) -1-1-onto-> ( A .o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cF
    cB
    cA
    cxp
    #
    wfn
    #
    cF
    ccnv
    #
    cA
    cB
    comu
    co
    #
    wfn
    #
    @3
    @6
    cF
    wf1o
    @2
    @3
    @6
    cF
    wf
    #
    @4
    @2
    cA
    vx
    cv
    #
    comu
    co
    #
    vy
    cv
    #
    coa
    co
    #
    @6
    wcel
    #
    vy
    cA
    wral
    vx
    cB
    wral
    @8
    @2
    @13
    vx
    vy
    cB
    cA
    @2
    @9
    cB
    wcel
    #
    @11
    cA
    wcel
    #
    wa
    #
    wa
    #
    cA
    @9
    csuc
    #
    comu
    co
    #
    @6
    @12
    @17
    @18
    cB
    wss
    #
    @19
    @6
    wss
    #
    @17
    cB
    word
    #
    @14
    @20
    @1
    @22
    @0
    @16
    cB
    eloni
    ad2antlr
    @2
    @14
    @15
    simprl
    @9
    cB
    ordsucss
    sylc
    @17
    @18
    con0
    wcel
    #
    @1
    @0
    @20
    @21
    wi
    @17
    @9
    con0
    wcel
    #
    @23
    @1
    @14
    @24
    @0
    @15
    cB
    @9
    onelon
    #
    ad2ant2lr
    #
    @9
    suceloni
    syl
    @0
    @1
    @16
    simplr
    @0
    @1
    @16
    simpll
    #
    @18
    cB
    cA
    omwordi
    syl3anc
    mpd
    @17
    @12
    @10
    cA
    coa
    co
    #
    @19
    @17
    @15
    @12
    @28
    wcel
    #
    @2
    @14
    @15
    simprr
    @17
    @11
    con0
    wcel
    #
    @0
    @10
    con0
    wcel
    #
    @15
    @29
    wb
    @0
    @15
    @30
    @1
    @14
    cA
    @11
    onelon
    #
    ad2ant2rl
    @27
    @17
    @0
    @24
    @31
    @27
    @26
    cA
    @9
    omcl
    #
    syl2anc
    @11
    cA
    @10
    oaord
    syl3anc
    mpbid
    @17
    @0
    @24
    @19
    @28
    wceq
    @27
    @26
    cA
    @9
    omsuc
    syl2anc
    eleqtrrd
    sseldd
    ralrimivva
    vx
    vy
    cB
    cA
    @12
    @6
    cF
    omxpenlem.1
    fmpt2
    sylib
    #
    @3
    @6
    cF
    ffn
    syl
    @2
    @5
    @6
    cres
    #
    @6
    wfn
    #
    @7
    @2
    vm
    cv
    #
    vn
    cv
    #
    @5
    wbr
    #
    vn
    weu
    #
    vm
    @6
    wral
    @36
    @2
    @40
    vm
    @6
    @2
    @37
    @6
    wcel
    #
    wa
    #
    @40
    @38
    @9
    @11
    cop
    wceq
    #
    @12
    @37
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    vx
    con0
    wrex
    #
    vn
    weu
    #
    @42
    @0
    @37
    con0
    wcel
    #
    cA
    c0
    wne
    #
    @47
    @0
    @1
    @41
    simpll
    @2
    @6
    con0
    wcel
    #
    @41
    @48
    cA
    cB
    omcl
    #
    @6
    @37
    onelon
    sylan
    @2
    @41
    @49
    @1
    @41
    @49
    wi
    @0
    @1
    @41
    cA
    c0
    @1
    cA
    c0
    wceq
    #
    @41
    wn
    @1
    @52
    wa
    #
    @41
    @37
    c0
    wcel
    @37
    noel
    @53
    @6
    c0
    @37
    @52
    @1
    @6
    c0
    cB
    comu
    co
    c0
    cA
    c0
    cB
    comu
    oveq1
    cB
    om0r
    sylan9eqr
    eleq2d
    mtbiri
    ex
    necon2ad
    adantl
    imp
    vx
    vy
    vn
    cA
    @37
    omeu
    syl3anc
    @42
    @39
    @46
    vn
    @39
    @38
    @37
    cF
    wbr
    #
    @42
    @46
    @37
    @38
    cF
    vm
    vex
    vn
    vex
    brcnv
    @42
    @43
    @16
    @37
    @12
    wceq
    #
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @24
    @15
    wa
    #
    @45
    wa
    #
    vy
    wex
    vx
    wex
    @54
    @46
    @42
    @57
    @60
    vx
    vy
    @42
    @57
    @43
    @59
    @44
    wa
    #
    wa
    @60
    @42
    @56
    @61
    @43
    @42
    @56
    @59
    @55
    wa
    @61
    @42
    @55
    @16
    @59
    @2
    @41
    @55
    @16
    @59
    wb
    #
    @41
    @55
    wa
    @2
    @13
    @62
    @55
    @41
    @13
    @37
    @12
    @6
    eleq1
    biimpac
    @2
    @13
    wa
    @15
    @14
    @24
    @2
    @13
    @15
    @14
    @24
    wb
    @2
    @13
    @15
    wa
    #
    wa
    #
    @14
    @24
    @1
    @14
    @24
    wi
    @0
    @63
    @1
    @14
    @24
    @25
    ex
    ad2antlr
    @64
    @24
    @14
    @64
    @24
    wa
    #
    @14
    @10
    @6
    wcel
    #
    @65
    @10
    @12
    wss
    #
    @13
    @66
    @65
    @31
    @30
    @67
    @65
    @0
    @24
    @31
    @0
    @1
    @63
    @24
    simplll
    #
    @64
    @24
    simpr
    #
    @33
    syl2anc
    #
    @65
    @0
    @15
    @30
    @68
    @2
    @13
    @15
    @24
    simplrr
    @32
    syl2anc
    @10
    @11
    oaword1
    syl2anc
    @2
    @13
    @15
    @24
    simplrl
    #
    @65
    @31
    @50
    @67
    @13
    wa
    @66
    wi
    @70
    @2
    @50
    @63
    @24
    @51
    ad2antrr
    #
    @10
    @12
    @6
    ontr2
    syl2anc
    mp2and
    @65
    @24
    @1
    @0
    c0
    cA
    wcel
    #
    @14
    @66
    wb
    @69
    @0
    @1
    @63
    @24
    simpllr
    @68
    @65
    @73
    c0
    cB
    wcel
    #
    @65
    c0
    @6
    wcel
    #
    @73
    @74
    wa
    #
    @65
    @75
    @6
    c0
    wne
    #
    @65
    @13
    @77
    @71
    @6
    @12
    ne0i
    syl
    @65
    @50
    @75
    @77
    wb
    @72
    @6
    on0eln0
    syl
    mpbird
    @2
    @75
    @76
    wb
    @63
    @24
    cA
    cB
    om00el
    ad2antrr
    mpbid
    simpld
    @9
    cB
    cA
    omord2
    syl31anc
    mpbird
    ex
    impbid
    expr
    pm5.32rd
    sylan2
    expr
    pm5.32rd
    @55
    @44
    @59
    @37
    @12
    eqcom
    anbi2i
    syl6bb
    anbi2d
    @43
    @59
    @44
    an12
    syl6bb
    2exbidv
    @54
    @38
    @37
    @58
    vn
    vm
    copab
    #
    wbr
    @38
    @37
    cop
    @78
    wcel
    @58
    @38
    @37
    cF
    @78
    cF
    vx
    vy
    cB
    cA
    @12
    cmpt2
    @56
    vx
    vy
    vm
    coprab
    @78
    omxpenlem.1
    vx
    vy
    vm
    cB
    cA
    @12
    df-mpt2
    @56
    vx
    vy
    vm
    vn
    dfoprab2
    3eqtri
    breqi
    @38
    @37
    @78
    df-br
    @58
    vn
    vm
    opabid
    3bitri
    @45
    vx
    vy
    con0
    cA
    r2ex
    3bitr4g
    syl5bb
    eubidv
    mpbird
    ralrimiva
    vm
    vn
    @6
    @5
    fnres
    sylibr
    @2
    @6
    @35
    @5
    @2
    @5
    wrel
    @5
    cdm
    #
    @6
    wss
    @35
    @5
    wceq
    cF
    relcnv
    @2
    @79
    cF
    crn
    #
    @6
    cF
    df-rn
    @2
    @8
    @80
    @6
    wss
    @34
    @3
    @6
    cF
    frn
    syl
    syl5eqssr
    @5
    @6
    relssres
    sylancr
    fneq1d
    mpbid
    @3
    @6
    cF
    dff1o4
    sylanbrc
end
