include "cz.mm"
include "cn0.mm"
include "cpw.mm"
include "cbits.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "bitsf.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cn.mm"
include "cc.mm"
include "simpl.mm"
include "zcnd.mm"
include "adantr.mm"
include "simpr.mm"
include "c1.mm"
include "negcld.mm"
include "1cnd.mm"
include "cmin.mm"
include "co.mm"
include "cres.mm"
include "cdif.mm"
include "simprr.mm"
include "difeq2d.mm"
include "bitscmp.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "3eqtr3d.mm"
include "nnm1nn0.mm"
include "ad2antrl.mm"
include "fvres.mm"
include "syl.mm"
include "cfn.mm"
include "wn.mm"
include "com.mm"
include "ominf.mm"
include "cen.mm"
include "wbr.mm"
include "nn0ennn.mm"
include "nnenom.mm"
include "entr2i.mm"
include "enfii.mm"
include "mpan2.mm"
include "mto.mm"
include "difinf.mm"
include "mpan.mm"
include "bitsfi.mm"
include "eqeltrd.mm"
include "nsyl3.mm"
include "eqneltrrd.mm"
include "nsyl.mm"
include "wo.mm"
include "znegcld.mm"
include "cr.mm"
include "elznn.mm"
include "simprbi.mm"
include "negnegd.mm"
include "eleq1d.mm"
include "orbi2d.mm"
include "mpbid.mm"
include "ord.mm"
include "mt3d.mm"
include "3eqtr4d.mm"
include "wb.mm"
include "cin.mm"
include "wf1o.mm"
include "bitsf1o.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "f1fveq.mm"
include "syl2anc.mm"
include "subcan2d.mm"
include "neg11d.mm"
include "expr.mm"
include "biimpa.mm"
include "eqeltrrd.mm"
include "sylancr.mm"
include "mpd.mm"
include "simprl.mm"
include "syldan.mm"
include "mpjaodan.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem bitsf1
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cN: class N


  assert |- bits : ZZ -1-1-> ~P NN0

  proof
    cz
    cn0
    cpw
    #
    cbits
    wf1
    cz
    @0
    cbits
    wf
    vx
    cv
    #
    cbits
    cfv
    #
    vy
    cv
    #
    cbits
    cfv
    #
    wceq
    #
    @1
    @3
    wceq
    #
    wi
    #
    vy
    cz
    wral
    vx
    cz
    wral
    bitsf
    @7
    vx
    vy
    cz
    @1
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    wa
    #
    @1
    cneg
    #
    cn
    wcel
    #
    @7
    @11
    cneg
    #
    cn0
    wcel
    #
    @10
    @12
    @5
    @6
    @10
    @12
    @5
    wa
    #
    wa
    #
    @1
    @3
    @10
    @1
    cc
    wcel
    @15
    @10
    @1
    @8
    @9
    simpl
    #
    zcnd
    #
    adantr
    #
    @10
    @3
    cc
    wcel
    @15
    @10
    @3
    @8
    @9
    simpr
    #
    zcnd
    #
    adantr
    #
    @16
    @11
    @3
    cneg
    #
    c1
    @16
    @1
    @19
    negcld
    @16
    @3
    @22
    negcld
    @16
    1cnd
    @16
    @11
    c1
    cmin
    co
    #
    cbits
    cn0
    cres
    #
    cfv
    #
    @23
    c1
    cmin
    co
    #
    @25
    cfv
    #
    wceq
    #
    @24
    @27
    wceq
    #
    @16
    @24
    cbits
    cfv
    #
    @27
    cbits
    cfv
    #
    @26
    @28
    @16
    cn0
    @2
    cdif
    #
    cn0
    @4
    cdif
    #
    @31
    @32
    @16
    @2
    @4
    cn0
    @10
    @12
    @5
    simprr
    #
    difeq2d
    @8
    @33
    @31
    wceq
    @9
    @15
    @1
    bitscmp
    ad2antrr
    #
    @9
    @34
    @32
    wceq
    #
    @8
    @15
    @3
    bitscmp
    #
    ad2antlr
    3eqtr3d
    @16
    @24
    cn0
    wcel
    #
    @26
    @31
    wceq
    @12
    @39
    @10
    @5
    @11
    nnm1nn0
    ad2antrl
    #
    @24
    cn0
    cbits
    fvres
    syl
    @16
    @27
    cn0
    wcel
    #
    @28
    @32
    wceq
    @16
    @23
    cn
    wcel
    #
    @41
    @16
    @42
    @3
    cn0
    wcel
    #
    @16
    @4
    cfn
    wcel
    #
    @43
    @16
    @2
    @4
    cfn
    @35
    @2
    cfn
    wcel
    #
    @33
    cfn
    wcel
    #
    @16
    cn0
    cfn
    wcel
    #
    wn
    #
    @45
    @46
    wn
    @47
    com
    cfn
    wcel
    #
    ominf
    @47
    com
    cn0
    cen
    wbr
    @49
    cn0
    cn
    com
    nn0ennn
    nnenom
    entr2i
    com
    cn0
    enfii
    mpan2
    mto
    #
    cn0
    @2
    difinf
    mpan
    @16
    @33
    @31
    cfn
    @36
    @16
    @39
    @31
    cfn
    wcel
    @40
    @24
    bitsfi
    syl
    eqeltrd
    nsyl3
    eqneltrrd
    @3
    bitsfi
    nsyl
    @16
    @42
    @43
    @10
    @42
    @43
    wo
    #
    @15
    @10
    @42
    @23
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    @51
    @10
    @23
    cz
    wcel
    #
    @54
    @10
    @3
    @20
    znegcld
    @55
    @23
    cr
    wcel
    @54
    @23
    elznn
    simprbi
    syl
    @10
    @53
    @43
    @42
    @10
    @52
    @3
    cn0
    @10
    @3
    @21
    negnegd
    eleq1d
    orbi2d
    mpbid
    #
    adantr
    ord
    mt3d
    @23
    nnm1nn0
    #
    syl
    #
    @27
    cn0
    cbits
    fvres
    syl
    3eqtr4d
    @16
    @39
    @41
    @29
    @30
    wb
    #
    @40
    @58
    cn0
    @0
    cfn
    cin
    #
    @25
    wf1
    #
    @39
    @41
    wa
    @59
    cn0
    @60
    @25
    wf1o
    @61
    bitsf1o
    cn0
    @60
    @25
    f1of1
    ax-mp
    #
    cn0
    @60
    @24
    @27
    @25
    f1fveq
    mpan
    syl2anc
    mpbid
    subcan2d
    neg11d
    expr
    @10
    @14
    @1
    cn0
    wcel
    #
    @7
    @10
    @14
    @63
    @10
    @13
    @1
    cn0
    @10
    @1
    @18
    negnegd
    eleq1d
    biimpa
    @10
    @63
    @5
    @6
    @10
    @63
    @5
    wa
    #
    wa
    #
    @1
    @25
    cfv
    #
    @3
    @25
    cfv
    #
    wceq
    #
    @6
    @65
    @2
    @4
    @66
    @67
    @10
    @63
    @5
    simprr
    #
    @63
    @66
    @2
    wceq
    @10
    @5
    @1
    cn0
    cbits
    fvres
    ad2antrl
    @65
    @43
    @67
    @4
    wceq
    @65
    @42
    wn
    @43
    @65
    @41
    @42
    @65
    @32
    cfn
    wcel
    @41
    @65
    @34
    @32
    cfn
    @9
    @37
    @8
    @64
    @38
    ad2antlr
    @65
    @48
    @44
    @34
    cfn
    wcel
    wn
    @50
    @65
    @2
    @4
    cfn
    @69
    @63
    @45
    @10
    @5
    @1
    bitsfi
    ad2antrl
    eqeltrrd
    cn0
    @4
    difinf
    sylancr
    eqneltrrd
    @27
    bitsfi
    nsyl
    @57
    nsyl
    @65
    @42
    @43
    @10
    @51
    @64
    @56
    adantr
    ord
    mpd
    #
    @3
    cn0
    cbits
    fvres
    syl
    3eqtr4d
    @65
    @63
    @43
    @68
    @6
    wb
    #
    @10
    @63
    @5
    simprl
    @70
    @61
    @63
    @43
    wa
    @71
    @62
    cn0
    @60
    @1
    @3
    @25
    f1fveq
    mpan
    syl2anc
    mpbid
    expr
    syldan
    @10
    @11
    cz
    wcel
    #
    @12
    @14
    wo
    #
    @10
    @1
    @17
    znegcld
    @72
    @11
    cr
    wcel
    @73
    @11
    elznn
    simprbi
    syl
    mpjaodan
    rgen2a
    vx
    vy
    cz
    @0
    cbits
    dff13
    mpbir2an
end
