include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cle.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "flltp1.mm"
include "ad3antrrr.mm"
include "wceq.mm"
include "cv.mm"
include "cz.mm"
include "crio.mm"
include "renegcl.mm"
include "flval.mm"
include "syl.mm"
include "ad3antlr.mm"
include "wi.mm"
include "fllep1.mm"
include "adantl.mm"
include "reflcl.mm"
include "peano2re.mm"
include "letr.mm"
include "mpd3an3.mm"
include "mpan2d.mm"
include "wb.mm"
include "leneg.mm"
include "sylan2.mm"
include "sylibd.mm"
include "ancoms.mm"
include "ltneg.mm"
include "sylan.mm"
include "cc.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "cmin.mm"
include "negdi2.mm"
include "oveq1d.mm"
include "negcl.mm"
include "npcan.mm"
include "eqtr2d.mm"
include "sylancl.mm"
include "breq2d.mm"
include "adantr.mm"
include "bitrd.mm"
include "biimpd.mm"
include "anim12d.mm"
include "ancomsd.mm"
include "impl.mm"
include "wreu.mm"
include "flcl.mm"
include "peano2zd.mm"
include "znegcld.mm"
include "rebtwnz.mm"
include "breq1.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "zcnd.mm"
include "peano2cn.mm"
include "flcld.mm"
include "negcon2.mm"
include "mpbird.mm"
include "breqtrd.mm"
include "ex.mm"
include "wn.mm"
include "ltnle.mm"
include "ceige.mm"
include "ceicl.mm"
include "zred.mm"
include "ltletr.mm"
include "sylbird.mm"
include "pm2.61d.mm"
include "ceim1l.mm"
include "peano2rem.mm"
include "ltleletr.mm"
include "3com13.mm"
include "mpand.mm"
include "biimprd.mm"
include "peano2zm.mm"
include "syl2anr.mm"
include "eqbrtrd.mm"
include "flle.mm"
include "lelttr.mm"
include "3coml.mm"
include "impbida.mm"

theorem ltflcei
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( |_ ` A ) < B <-> A < -u ( |_ ` -u B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cfl
    cfv
    #
    cB
    clt
    wbr
    #
    cA
    cB
    cneg
    #
    cfl
    cfv
    #
    cneg
    #
    clt
    wbr
    #
    @2
    @4
    wa
    #
    cB
    cA
    cle
    wbr
    #
    @8
    @9
    @10
    @8
    @9
    @10
    wa
    #
    cA
    @3
    c1
    caddc
    co
    #
    @7
    clt
    @0
    cA
    @12
    clt
    wbr
    @1
    @4
    @10
    cA
    flltp1
    ad3antrrr
    @11
    @12
    @7
    wceq
    #
    @6
    @12
    cneg
    #
    wceq
    #
    @11
    @6
    vx
    cv
    #
    @5
    cle
    wbr
    #
    @5
    @16
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    cz
    crio
    #
    @14
    @1
    @6
    @21
    wceq
    #
    @0
    @4
    @10
    @1
    @5
    cr
    wcel
    #
    @22
    cB
    renegcl
    #
    vx
    @5
    flval
    syl
    ad3antlr
    @11
    @14
    @5
    cle
    wbr
    #
    @5
    @14
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @21
    @14
    wceq
    #
    @2
    @4
    @10
    @28
    @2
    @10
    @4
    @28
    @2
    @10
    @25
    @4
    @27
    @1
    @0
    @10
    @25
    wi
    @1
    @0
    wa
    #
    @10
    cB
    @12
    cle
    wbr
    #
    @25
    @30
    @10
    cA
    @12
    cle
    wbr
    #
    @31
    @0
    @32
    @1
    cA
    fllep1
    adantl
    @1
    @0
    @12
    cr
    wcel
    #
    @10
    @32
    wa
    @31
    wi
    @0
    @33
    @1
    @0
    @3
    cr
    wcel
    #
    @33
    cA
    reflcl
    #
    @3
    peano2re
    syl
    #
    adantl
    cB
    cA
    @12
    letr
    mpd3an3
    mpan2d
    @0
    @1
    @33
    @31
    @25
    wb
    @36
    cB
    @12
    leneg
    sylan2
    sylibd
    ancoms
    @2
    @4
    @27
    @2
    @4
    @5
    @3
    cneg
    #
    clt
    wbr
    #
    @27
    @0
    @34
    @1
    @4
    @38
    wb
    @35
    @3
    cB
    ltneg
    sylan
    @0
    @38
    @27
    wb
    @1
    @0
    @37
    @26
    @5
    clt
    @0
    @3
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @37
    @26
    wceq
    @0
    @3
    @35
    recnd
    ax-1cn
    @39
    @40
    wa
    #
    @26
    @37
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @37
    @41
    @14
    @42
    c1
    caddc
    @3
    c1
    negdi2
    oveq1d
    @39
    @37
    cc
    wcel
    @40
    @43
    @37
    wceq
    @3
    negcl
    @37
    c1
    npcan
    sylan
    eqtr2d
    sylancl
    breq2d
    adantr
    bitrd
    biimpd
    anim12d
    ancomsd
    impl
    @2
    @28
    @29
    wb
    #
    @4
    @10
    @0
    @14
    cz
    wcel
    @20
    vx
    cz
    wreu
    #
    @44
    @1
    @0
    @12
    @0
    @3
    cA
    flcl
    #
    peano2zd
    znegcld
    @1
    @23
    @45
    @24
    vx
    @5
    rebtwnz
    syl
    @20
    @28
    vx
    cz
    @14
    @16
    @14
    wceq
    #
    @17
    @25
    @19
    @27
    @16
    @14
    @5
    cle
    breq1
    @47
    @18
    @26
    @5
    clt
    @16
    @14
    c1
    caddc
    oveq1
    breq2d
    anbi12d
    riota2
    syl2an
    ad2antrr
    mpbid
    eqtrd
    @2
    @13
    @15
    wb
    #
    @4
    @10
    @0
    @12
    cc
    wcel
    #
    @6
    cc
    wcel
    @48
    @1
    @0
    @39
    @49
    @0
    @3
    @46
    zcnd
    @3
    peano2cn
    syl
    @1
    @6
    @1
    @5
    @24
    flcld
    zcnd
    @12
    @6
    negcon2
    syl2an
    ad2antrr
    mpbird
    breqtrd
    ex
    @2
    @10
    wn
    #
    @8
    wi
    @4
    @2
    @50
    cA
    cB
    clt
    wbr
    #
    @8
    cA
    cB
    ltnle
    #
    @2
    @51
    cB
    @7
    cle
    wbr
    #
    @8
    @1
    @53
    @0
    cB
    ceige
    adantl
    @0
    @1
    @7
    cr
    wcel
    #
    @51
    @53
    wa
    @8
    wi
    @1
    @54
    @0
    @1
    @7
    cB
    ceicl
    #
    zred
    #
    adantl
    cA
    cB
    @7
    ltletr
    mpd3an3
    mpan2d
    sylbird
    adantr
    pm2.61d
    @2
    @8
    wa
    #
    @10
    @4
    @57
    @10
    @4
    @57
    @10
    wa
    #
    @3
    @7
    c1
    cmin
    co
    #
    cB
    clt
    @58
    @3
    @16
    cA
    cle
    wbr
    #
    cA
    @18
    clt
    wbr
    #
    wa
    #
    vx
    cz
    crio
    #
    @59
    @0
    @3
    @63
    wceq
    @1
    @8
    @10
    vx
    cA
    flval
    ad3antrrr
    @58
    @59
    cA
    cle
    wbr
    #
    cA
    @59
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @63
    @59
    wceq
    #
    @2
    @8
    @10
    @67
    @2
    @10
    @8
    @67
    @2
    @10
    @64
    @8
    @66
    @2
    @59
    cB
    clt
    wbr
    #
    @10
    @64
    @1
    @69
    @0
    cB
    ceim1l
    #
    adantl
    @0
    @1
    @59
    cr
    wcel
    #
    @69
    @10
    wa
    @64
    wi
    #
    @1
    @71
    @0
    @1
    @54
    @71
    @56
    @7
    peano2rem
    syl
    adantl
    @71
    @1
    @0
    @72
    @59
    cB
    cA
    ltleletr
    3com13
    mpd3an3
    mpand
    @1
    @8
    @66
    wi
    @0
    @1
    @66
    @8
    @1
    @65
    @7
    cA
    clt
    @1
    @7
    cc
    wcel
    @40
    @65
    @7
    wceq
    @1
    @7
    @55
    zcnd
    ax-1cn
    @7
    c1
    npcan
    sylancl
    breq2d
    biimprd
    adantl
    anim12d
    ancomsd
    impl
    @2
    @67
    @68
    wb
    #
    @8
    @10
    @1
    @59
    cz
    wcel
    #
    @62
    vx
    cz
    wreu
    @73
    @0
    @1
    @7
    cz
    wcel
    @74
    @55
    @7
    peano2zm
    syl
    vx
    cA
    rebtwnz
    @62
    @67
    vx
    cz
    @59
    @16
    @59
    wceq
    #
    @60
    @64
    @61
    @66
    @16
    @59
    cA
    cle
    breq1
    @75
    @18
    @65
    cA
    clt
    @16
    @59
    c1
    caddc
    oveq1
    breq2d
    anbi12d
    riota2
    syl2anr
    ad2antrr
    mpbid
    eqtrd
    @1
    @69
    @0
    @8
    @10
    @70
    ad3antlr
    eqbrtrd
    ex
    @2
    @50
    @4
    wi
    @8
    @2
    @50
    @51
    @4
    @52
    @2
    @3
    cA
    cle
    wbr
    #
    @51
    @4
    @0
    @76
    @1
    cA
    flle
    adantr
    @0
    @1
    @34
    @76
    @51
    wa
    @4
    wi
    #
    @0
    @34
    @1
    @35
    adantr
    @34
    @0
    @1
    @77
    @3
    cA
    cB
    lelttr
    3coml
    mpd3an3
    mpand
    sylbird
    adantr
    pm2.61d
    impbida
end
