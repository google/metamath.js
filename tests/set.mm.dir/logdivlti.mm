include "cr.mm"
include "wcel.mm"
include "ceu.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "clt.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "c1.mm"
include "crp.mm"
include "simpl2.mm"
include "cc0.mm"
include "simpl3.mm"
include "simpr.mm"
include "wi.mm"
include "simpl1.mm"
include "ere.mm"
include "lelttr.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "mp2and.mm"
include "epos.mm"
include "0re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "syl.mm"
include "mpani.mm"
include "mpd.mm"
include "elrpd.mm"
include "ltletr.mm"
include "rpdivcld.mm"
include "relogcl.mm"
include "rerpdivcld.mm"
include "1re.mm"
include "resubcl.mm"
include "sylancl.mm"
include "remulcld.mm"
include "ce.mm"
include "caddc.mm"
include "wceq.mm"
include "reeflog.mm"
include "cc.mm"
include "ax-1cn.mm"
include "recnd.mm"
include "pncan3.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "mulid2d.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "1red.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "difrp.mm"
include "efgt1p.mm"
include "eflt.mm"
include "mpbird.mm"
include "mulid1d.mm"
include "df-e.mm"
include "breqtrrd.mm"
include "syl5eqbrr.mm"
include "efle.mm"
include "posdif.mm"
include "lemul2.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "relogdiv.mm"
include "1cnd.mm"
include "subdird.mm"
include "rpne0d.mm"
include "div32d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3brtr3d.mm"
include "ltsub1d.mm"
include "ltdivmuld.mm"

theorem logdivlti
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR /\ _e <_ A ) /\ A < B ) -> ( ( log ` B ) / B ) < ( ( log ` A ) / A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    ceu
    cA
    cle
    wbr
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    cB
    clog
    cfv
    #
    cB
    cdiv
    co
    cA
    clog
    cfv
    #
    cA
    cdiv
    co
    #
    clt
    wbr
    @6
    cB
    @8
    cmul
    co
    #
    clt
    wbr
    #
    @5
    @10
    @6
    @7
    cmin
    co
    #
    @9
    @7
    cmin
    co
    #
    clt
    wbr
    @5
    cB
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    @13
    c1
    cmin
    co
    #
    @7
    cmul
    co
    #
    @11
    @12
    clt
    @5
    @14
    @15
    @16
    @5
    @13
    crp
    wcel
    #
    @14
    cr
    wcel
    #
    @5
    cB
    cA
    @5
    cB
    @0
    @1
    @2
    @4
    simpl2
    #
    @5
    ceu
    cB
    clt
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    @5
    @2
    @4
    @20
    @0
    @1
    @2
    @4
    simpl3
    #
    @3
    @4
    simpr
    #
    @5
    @0
    @1
    @2
    @4
    wa
    @20
    wi
    #
    @0
    @1
    @2
    @4
    simpl1
    #
    @19
    ceu
    cr
    wcel
    #
    @0
    @1
    @24
    ere
    ceu
    cA
    cB
    lelttr
    mp3an1
    syl2anc
    mp2and
    @5
    cc0
    ceu
    clt
    wbr
    #
    @20
    @21
    epos
    @5
    @1
    @27
    @20
    wa
    @21
    wi
    #
    @19
    cc0
    cr
    wcel
    #
    @26
    @1
    @28
    0re
    ere
    cc0
    ceu
    cB
    lttr
    mp3an12
    syl
    mpani
    mpd
    elrpd
    #
    @5
    cA
    @25
    @5
    @2
    cc0
    cA
    clt
    wbr
    #
    @22
    @5
    @27
    @2
    @31
    epos
    @5
    @0
    @27
    @2
    wa
    @31
    wi
    #
    @25
    @29
    @26
    @0
    @32
    0re
    ere
    cc0
    ceu
    cA
    ltletr
    mp3an12
    syl
    mpani
    mpd
    #
    elrpd
    #
    rpdivcld
    #
    @13
    relogcl
    syl
    #
    @5
    @13
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @5
    cB
    cA
    @19
    @34
    rerpdivcld
    #
    1re
    @13
    c1
    resubcl
    sylancl
    #
    @5
    @15
    @7
    @41
    @5
    cA
    crp
    wcel
    #
    @7
    cr
    wcel
    #
    @34
    cA
    relogcl
    syl
    #
    remulcld
    @5
    @14
    @15
    clt
    wbr
    #
    @14
    ce
    cfv
    #
    @15
    ce
    cfv
    #
    clt
    wbr
    #
    @5
    @46
    c1
    @15
    caddc
    co
    #
    @47
    clt
    @5
    @46
    @13
    @49
    @5
    @17
    @46
    @13
    wceq
    @35
    @13
    reeflog
    syl
    @5
    c1
    cc
    wcel
    @13
    cc
    wcel
    @49
    @13
    wceq
    ax-1cn
    @5
    @13
    @40
    recnd
    #
    c1
    @13
    pncan3
    sylancr
    eqtr4d
    @5
    @15
    crp
    wcel
    #
    @49
    @47
    clt
    wbr
    @5
    c1
    @13
    clt
    wbr
    #
    @51
    @5
    c1
    cA
    cmul
    co
    #
    cB
    clt
    wbr
    #
    @52
    @5
    @53
    cA
    cB
    clt
    @5
    cA
    @5
    cA
    @25
    recnd
    #
    mulid2d
    @23
    eqbrtrd
    @5
    @38
    @1
    @0
    @31
    @54
    @52
    wb
    @5
    1red
    #
    @19
    @25
    @33
    c1
    cB
    cA
    ltmuldiv
    syl112anc
    mpbid
    #
    @5
    @38
    @37
    @52
    @51
    wb
    1re
    @40
    c1
    @13
    difrp
    sylancr
    mpbid
    @15
    efgt1p
    syl
    eqbrtrd
    @5
    @18
    @39
    @45
    @48
    wb
    @36
    @41
    @14
    @15
    eflt
    syl2anc
    mpbird
    @5
    @15
    c1
    cmul
    co
    #
    @15
    @16
    cle
    @5
    @15
    @5
    @15
    @41
    recnd
    mulid1d
    @5
    c1
    @7
    cle
    wbr
    #
    @58
    @16
    cle
    wbr
    #
    @5
    @59
    c1
    ce
    cfv
    #
    @7
    ce
    cfv
    #
    cle
    wbr
    #
    @5
    @61
    ceu
    @62
    cle
    df-e
    @5
    ceu
    cA
    @62
    cle
    @22
    @5
    @42
    @62
    cA
    wceq
    @34
    cA
    reeflog
    syl
    breqtrrd
    syl5eqbrr
    @5
    @38
    @43
    @59
    @63
    wb
    1re
    @44
    c1
    @7
    efle
    sylancr
    mpbird
    @5
    @38
    @43
    @39
    cc0
    @15
    clt
    wbr
    #
    @59
    @60
    wb
    @56
    @44
    @41
    @5
    @52
    @64
    @57
    @5
    @38
    @37
    @52
    @64
    wb
    1re
    @40
    c1
    @13
    posdif
    sylancr
    mpbid
    c1
    @7
    @15
    lemul2
    syl112anc
    mpbid
    eqbrtrrd
    ltletrd
    @5
    cB
    crp
    wcel
    #
    @42
    @14
    @11
    wceq
    @30
    @34
    cB
    cA
    relogdiv
    syl2anc
    @5
    @16
    @13
    @7
    cmul
    co
    #
    c1
    @7
    cmul
    co
    #
    cmin
    co
    @12
    @5
    @13
    c1
    @7
    @50
    @5
    1cnd
    @5
    @7
    @44
    recnd
    #
    subdird
    @5
    @66
    @9
    @67
    @7
    cmin
    @5
    cB
    cA
    @7
    @5
    cB
    @19
    recnd
    @55
    @68
    @5
    cA
    @34
    rpne0d
    div32d
    @5
    @7
    @68
    mulid2d
    oveq12d
    eqtrd
    3brtr3d
    @5
    @6
    @9
    @7
    @5
    @65
    @6
    cr
    wcel
    @30
    cB
    relogcl
    syl
    #
    @5
    cB
    @8
    @19
    @5
    @7
    cA
    @44
    @34
    rerpdivcld
    #
    remulcld
    @44
    ltsub1d
    mpbird
    @5
    @6
    @8
    cB
    @69
    @70
    @30
    ltdivmuld
    mpbird
end
