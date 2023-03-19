include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wa.mm"
include "csin.mm"
include "casin.mm"
include "ci.mm"
include "cmul.mm"
include "c1.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "caddc.mm"
include "clog.mm"
include "wceq.mm"
include "sincl.mm"
include "adantr.mm"
include "asinval.mm"
include "syl.mm"
include "ce.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "simpl.mm"
include "efcl.mm"
include "pncan3d.mm"
include "subcld.mm"
include "ax-1cn.mm"
include "sqcld.mm"
include "subcl.mm"
include "binom2sub.mm"
include "syl2anc.mm"
include "ccos.mm"
include "sqvald.mm"
include "2cn.mm"
include "a1i.mm"
include "mul12d.mm"
include "oveq12d.mm"
include "coscl.mm"
include "subsq.mm"
include "sqmul.mm"
include "i2.mm"
include "oveq1i.mm"
include "mulm1d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "subnegd.mm"
include "addcomd.mm"
include "3eqtrd.mm"
include "efival.mm"
include "2timesd.mm"
include "pnpcan2d.mm"
include "subdid.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "sincossq.mm"
include "3eqtr2d.mm"
include "negsub.mm"
include "cc0.mm"
include "clt.mm"
include "cr.mm"
include "halfre.mm"
include "negicn.mm"
include "addcld.mm"
include "recld.mm"
include "wbr.mm"
include "halfgt0.mm"
include "asinsinlem.mm"
include "negcl.mm"
include "reneg.mm"
include "wb.mm"
include "recl.mm"
include "halfpire.mm"
include "renegcli.mm"
include "iooneg.mm"
include "mp3an12.mm"
include "biimpa.mm"
include "recni.mm"
include "negnegi.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "eqeltrd.mm"
include "mulneg12.mm"
include "fveq2d.mm"
include "breqtrrd.mm"
include "addgt0d.mm"
include "readdd.mm"
include "mulgt0d.mm"
include "cosval.mm"
include "wne.mm"
include "2ne0.mm"
include "divrec2d.mm"
include "remul2.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqsqrt2d.mm"
include "crn.mm"
include "cim.mm"
include "cle.mm"
include "pire.mm"
include "elioore.mm"
include "adantl.mm"
include "crp.mm"
include "pirp.mm"
include "rphalflt.mm"
include "ax-mp.mm"
include "ltnegi.mm"
include "mpbi.mm"
include "eliooord.mm"
include "simpld.mm"
include "lttrd.mm"
include "imre.mm"
include "mulneg1i.mm"
include "ixi.mm"
include "negeqi.mm"
include "3eqtri.mm"
include "mulassd.mm"
include "mulid2.mm"
include "3eqtr3a.mm"
include "simprd.mm"
include "ltled.mm"
include "eqbrtrd.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"
include "logef.mm"

theorem asinsin
  let cA: class A


  assert |- ( ( A e. CC /\ ( Re ` A ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) ) -> ( arcsin ` ( sin ` A ) ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @2
    cioo
    co
    #
    wcel
    #
    wa
    #
    cA
    csin
    cfv
    #
    casin
    cfv
    #
    ci
    cneg
    #
    ci
    @7
    cmul
    co
    #
    c1
    @7
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @9
    ci
    cA
    cmul
    co
    #
    cmul
    co
    #
    cA
    @6
    @7
    cc
    wcel
    #
    @8
    @16
    wceq
    @0
    @19
    @5
    cA
    sincl
    adantr
    #
    @7
    asinval
    syl
    @6
    @15
    @17
    @9
    cmul
    @6
    @17
    ce
    cfv
    #
    clog
    cfv
    #
    @15
    @17
    @6
    @21
    @14
    clog
    @6
    @10
    @21
    @10
    cmin
    co
    #
    caddc
    co
    @21
    @14
    @6
    @10
    @21
    @6
    ci
    cc
    wcel
    #
    @19
    @10
    cc
    wcel
    #
    ax-icn
    @20
    ci
    @7
    mulcl
    sylancr
    #
    @6
    @17
    cc
    wcel
    #
    @21
    cc
    wcel
    #
    @6
    @24
    @0
    @27
    ax-icn
    @0
    @5
    simpl
    #
    ci
    cA
    mulcl
    sylancr
    #
    @17
    efcl
    syl
    #
    pncan3d
    @6
    @23
    @13
    @10
    caddc
    @6
    @23
    @12
    @6
    @21
    @10
    @31
    @26
    subcld
    @6
    c1
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @12
    cc
    wcel
    ax-1cn
    @6
    @7
    @20
    sqcld
    #
    c1
    @11
    subcl
    sylancr
    @6
    @23
    c2
    cexp
    co
    #
    @21
    c2
    cexp
    co
    #
    c2
    @21
    @10
    cmul
    co
    cmul
    co
    #
    cmin
    co
    #
    @10
    c2
    cexp
    co
    #
    caddc
    co
    #
    c1
    @11
    cneg
    #
    caddc
    co
    #
    @12
    @6
    @28
    @25
    @35
    @40
    wceq
    @31
    @26
    @21
    @10
    binom2sub
    syl2anc
    @6
    @38
    c1
    @39
    @41
    caddc
    @6
    @38
    @21
    @21
    cmul
    co
    #
    @21
    c2
    @10
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @11
    cA
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c1
    @6
    @36
    @43
    @37
    @45
    cmin
    @6
    @21
    @31
    sqvald
    @6
    c2
    @21
    @10
    c2
    cc
    wcel
    #
    @6
    2cn
    a1i
    #
    @31
    @26
    mul12d
    oveq12d
    @6
    @48
    @39
    cmin
    co
    #
    @47
    @10
    caddc
    co
    #
    @47
    @10
    cmin
    co
    #
    cmul
    co
    #
    @49
    @46
    @6
    @47
    cc
    wcel
    #
    @25
    @52
    @55
    wceq
    @0
    @56
    @5
    cA
    coscl
    adantr
    #
    @26
    @47
    @10
    subsq
    syl2anc
    @6
    @52
    @48
    @41
    cmin
    co
    @48
    @11
    caddc
    co
    @49
    @6
    @39
    @41
    @48
    cmin
    @6
    @39
    ci
    c2
    cexp
    co
    #
    @11
    cmul
    co
    #
    @41
    @6
    @24
    @19
    @39
    @59
    wceq
    ax-icn
    @20
    ci
    @7
    sqmul
    sylancr
    @6
    @59
    c1
    cneg
    #
    @11
    cmul
    co
    @41
    @58
    @60
    @11
    cmul
    i2
    oveq1i
    @6
    @11
    @34
    mulm1d
    syl5eq
    eqtrd
    #
    oveq2d
    @6
    @48
    @11
    @6
    @47
    @57
    sqcld
    #
    @34
    subnegd
    @6
    @48
    @11
    @62
    @34
    addcomd
    3eqtrd
    @6
    @21
    @21
    @44
    cmin
    co
    #
    cmul
    co
    @55
    @46
    @6
    @21
    @53
    @63
    @54
    cmul
    @0
    @21
    @53
    wceq
    @5
    cA
    efival
    adantr
    #
    @6
    @63
    @53
    @10
    @10
    caddc
    co
    #
    cmin
    co
    @54
    @6
    @21
    @53
    @44
    @65
    cmin
    @64
    @6
    @10
    @26
    2timesd
    oveq12d
    @6
    @47
    @10
    @10
    @57
    @26
    @26
    pnpcan2d
    eqtrd
    oveq12d
    @6
    @21
    @21
    @44
    @31
    @31
    @6
    @50
    @25
    @44
    cc
    wcel
    2cn
    @26
    c2
    @10
    mulcl
    sylancr
    subdid
    eqtr3d
    3eqtr3d
    @0
    @49
    c1
    wceq
    @5
    cA
    sincossq
    adantr
    3eqtr2d
    @61
    oveq12d
    @6
    @32
    @33
    @42
    @12
    wceq
    ax-1cn
    @34
    c1
    @11
    negsub
    sylancr
    3eqtrd
    @6
    cc0
    @47
    cre
    cfv
    #
    @23
    cre
    cfv
    clt
    @6
    cc0
    c1
    c2
    cdiv
    co
    #
    @21
    @9
    cA
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    cre
    cfv
    #
    cmul
    co
    #
    @66
    clt
    @6
    @67
    @71
    @67
    cr
    wcel
    #
    @6
    halfre
    a1i
    @6
    @70
    @6
    @21
    @69
    @31
    @6
    @68
    cc
    wcel
    #
    @69
    cc
    wcel
    @6
    @9
    cc
    wcel
    #
    @0
    @74
    negicn
    @29
    @9
    cA
    mulcl
    sylancr
    @68
    efcl
    syl
    #
    addcld
    #
    recld
    cc0
    @67
    clt
    wbr
    @6
    halfgt0
    a1i
    @6
    cc0
    @21
    cre
    cfv
    #
    @69
    cre
    cfv
    #
    caddc
    co
    @71
    clt
    @6
    @78
    @79
    @6
    @21
    @31
    recld
    @6
    @69
    @76
    recld
    cA
    asinsinlem
    @6
    cc0
    ci
    cA
    cneg
    #
    cmul
    co
    #
    ce
    cfv
    #
    cre
    cfv
    #
    @79
    clt
    @6
    @80
    cc
    wcel
    #
    @80
    cre
    cfv
    #
    @4
    wcel
    cc0
    @83
    clt
    wbr
    @0
    @84
    @5
    cA
    negcl
    adantr
    @6
    @85
    @1
    cneg
    #
    @4
    @0
    @85
    @86
    wceq
    @5
    cA
    reneg
    adantr
    @6
    @86
    @3
    @3
    cneg
    #
    cioo
    co
    #
    @4
    @0
    @5
    @86
    @88
    wcel
    #
    @0
    @1
    cr
    wcel
    #
    @5
    @89
    wb
    #
    cA
    recl
    @3
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @90
    @91
    @2
    halfpire
    renegcli
    #
    halfpire
    @3
    @2
    @1
    iooneg
    mp3an12
    syl
    biimpa
    @87
    @2
    @3
    cioo
    @2
    @2
    halfpire
    recni
    negnegi
    oveq2i
    syl6eleq
    eqeltrd
    @80
    asinsinlem
    syl2anc
    @6
    @69
    @82
    cre
    @6
    @68
    @81
    ce
    @6
    @24
    @0
    @68
    @81
    wceq
    ax-icn
    @29
    ci
    cA
    mulneg12
    sylancr
    fveq2d
    fveq2d
    breqtrrd
    addgt0d
    @6
    @21
    @69
    @31
    @76
    readdd
    breqtrrd
    mulgt0d
    @6
    @66
    @67
    @70
    cmul
    co
    #
    cre
    cfv
    #
    @72
    @6
    @47
    @95
    cre
    @6
    @47
    @70
    c2
    cdiv
    co
    #
    @95
    @0
    @47
    @97
    wceq
    @5
    cA
    cosval
    adantr
    @6
    @70
    c2
    @77
    @51
    c2
    cc0
    wne
    @6
    2ne0
    a1i
    divrec2d
    eqtrd
    fveq2d
    @6
    @73
    @70
    cc
    wcel
    @96
    @72
    wceq
    halfre
    @77
    @67
    @70
    remul2
    sylancr
    eqtrd
    breqtrrd
    @6
    @23
    @47
    cre
    @6
    @23
    @53
    @10
    cmin
    co
    @47
    @6
    @21
    @53
    @10
    cmin
    @64
    oveq1d
    @6
    @47
    @10
    @57
    @26
    pncand
    eqtrd
    fveq2d
    breqtrrd
    eqsqrt2d
    oveq2d
    eqtr3d
    fveq2d
    @6
    @17
    clog
    crn
    wcel
    #
    @22
    @17
    wceq
    @6
    @27
    cpi
    cneg
    #
    @17
    cim
    cfv
    #
    clt
    wbr
    @100
    cpi
    cle
    wbr
    @98
    @30
    @6
    @99
    @1
    @100
    clt
    @6
    @99
    @3
    @1
    @99
    cr
    wcel
    @6
    cpi
    pire
    renegcli
    a1i
    @92
    @6
    @94
    a1i
    @5
    @90
    @0
    @1
    @3
    @2
    elioore
    adantl
    #
    @99
    @3
    clt
    wbr
    #
    @6
    @2
    cpi
    clt
    wbr
    #
    @102
    cpi
    crp
    wcel
    @103
    pirp
    cpi
    rphalflt
    ax-mp
    #
    @2
    cpi
    halfpire
    pire
    ltnegi
    mpbi
    a1i
    @6
    @3
    @1
    clt
    wbr
    #
    @1
    @2
    clt
    wbr
    #
    @5
    @105
    @106
    wa
    @0
    @1
    @3
    @2
    eliooord
    adantl
    #
    simpld
    lttrd
    @6
    @100
    @18
    cre
    cfv
    #
    @1
    @6
    @27
    @100
    @108
    wceq
    @30
    @17
    imre
    syl
    @6
    @18
    cA
    cre
    @6
    @9
    ci
    cmul
    co
    #
    cA
    cmul
    co
    c1
    cA
    cmul
    co
    #
    @18
    cA
    @109
    c1
    cA
    cmul
    @109
    ci
    ci
    cmul
    co
    #
    cneg
    @60
    cneg
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg1i
    @111
    @60
    ixi
    negeqi
    c1
    ax-1cn
    negnegi
    3eqtri
    oveq1i
    @6
    @9
    ci
    cA
    @75
    @6
    negicn
    a1i
    @24
    @6
    ax-icn
    a1i
    @29
    mulassd
    @0
    @110
    cA
    wceq
    @5
    cA
    mulid2
    adantr
    3eqtr3a
    #
    fveq2d
    eqtrd
    #
    breqtrrd
    @6
    @100
    @1
    cpi
    cle
    @113
    @6
    @1
    cpi
    @101
    cpi
    cr
    wcel
    @6
    pire
    a1i
    #
    @6
    @1
    @2
    cpi
    @101
    @93
    @6
    halfpire
    a1i
    @114
    @6
    @105
    @106
    @107
    simprd
    @103
    @6
    @104
    a1i
    lttrd
    ltled
    eqbrtrd
    @17
    ellogrn
    syl3anbrc
    @17
    logef
    syl
    eqtr3d
    oveq2d
    @112
    3eqtrd
end
