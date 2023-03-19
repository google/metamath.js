include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "c1.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clog.mm"
include "cmin.mm"
include "crn.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "cc.mm"
include "wne.mm"
include "atandm2.mm"
include "simp1bi.mm"
include "recld.mm"
include "leloe.mm"
include "sylancr.mm"
include "biimpa.mm"
include "wa.mm"
include "cpi.mm"
include "cneg.mm"
include "cim.mm"
include "ax-1cn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "addcl.mm"
include "simp3bi.mm"
include "logcld.mm"
include "subcl.mm"
include "simp2bi.mm"
include "addcld.mm"
include "adantr.mm"
include "pire.mm"
include "renegcli.mm"
include "a1i.mm"
include "imcld.mm"
include "readdcld.mm"
include "cioo.mm"
include "im1.mm"
include "oveq1i.mm"
include "df-neg.mm"
include "eqtr4i.mm"
include "imsub.mm"
include "reim.mm"
include "syl.mm"
include "negeqd.mm"
include "3eqtr4a.mm"
include "lt0neg2d.mm"
include "eqbrtrd.mm"
include "argimlt0.mm"
include "syl2anc.mm"
include "eliooord.mm"
include "simpld.mm"
include "simpr.mm"
include "imadd.mm"
include "oveq2d.mm"
include "recnd.mm"
include "addid2d.mm"
include "syl5eq.mm"
include "3eqtr2d.mm"
include "breqtrrd.mm"
include "argimgt0.mm"
include "ltaddpos2d.mm"
include "mpbid.mm"
include "lttrd.mm"
include "imaddd.mm"
include "0red.mm"
include "simprd.mm"
include "ltadd2dd.mm"
include "addid1d.mm"
include "breqtrd.mm"
include "ltled.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"
include "eqtr2d.mm"
include "reim0bd.mm"
include "addcomd.mm"
include "ad2antrr.mm"
include "logrncl.mm"
include "1re.mm"
include "readdcl.mm"
include "1red.mm"
include "0lt1.mm"
include "addge01.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "relogcld.mm"
include "logrnaddcl.mm"
include "eqeltrd.mm"
include "resubcl.mm"
include "1m0e1.mm"
include "lesub2d.mm"
include "syl5eqbrr.mm"
include "lecasei.mm"
include "jaodan.mm"
include "syldan.mm"

theorem atanlogaddlem
  let cA: class A


  assert |- ( ( A e. dom arctan /\ 0 <_ ( Re ` A ) ) -> ( ( log ` ( 1 + ( _i x. A ) ) ) + ( log ` ( 1 - ( _i x. A ) ) ) ) e. ran log )

  proof
    cA
    catan
    cdm
    wcel
    #
    cc0
    cA
    cre
    cfv
    #
    cle
    wbr
    #
    cc0
    @1
    clt
    wbr
    #
    cc0
    @1
    wceq
    #
    wo
    #
    c1
    ci
    cA
    cmul
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    c1
    @6
    cmin
    co
    #
    clog
    cfv
    #
    caddc
    co
    #
    clog
    crn
    #
    wcel
    #
    @0
    @2
    @5
    @0
    cc0
    cr
    wcel
    @1
    cr
    wcel
    @2
    @5
    wb
    0re
    @0
    cA
    @0
    cA
    cc
    wcel
    #
    @9
    cc0
    wne
    #
    @7
    cc0
    wne
    #
    cA
    atandm2
    #
    simp1bi
    #
    recld
    #
    cc0
    @1
    leloe
    sylancr
    biimpa
    @0
    @3
    @13
    @4
    @0
    @3
    wa
    #
    @11
    cc
    wcel
    #
    cpi
    cneg
    #
    @11
    cim
    cfv
    #
    clt
    wbr
    @23
    cpi
    cle
    wbr
    @13
    @0
    @21
    @3
    @0
    @8
    @10
    @0
    @7
    @0
    c1
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    ax-1cn
    @0
    ci
    cc
    wcel
    @14
    @25
    ax-icn
    @18
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @6
    addcl
    sylancr
    #
    @0
    @14
    @15
    @16
    @17
    simp3bi
    #
    logcld
    #
    @0
    @9
    @0
    @24
    @25
    @9
    cc
    wcel
    #
    ax-1cn
    @27
    c1
    @6
    subcl
    sylancr
    #
    @0
    @14
    @15
    @16
    @17
    simp2bi
    #
    logcld
    #
    addcld
    adantr
    @20
    @22
    @8
    cim
    cfv
    #
    @10
    cim
    cfv
    #
    caddc
    co
    #
    @23
    clt
    @20
    @22
    @36
    @37
    @22
    cr
    wcel
    @20
    cpi
    pire
    renegcli
    a1i
    @20
    @10
    @0
    @10
    cc
    wcel
    @3
    @34
    adantr
    #
    imcld
    #
    @20
    @35
    @36
    @20
    @8
    @0
    @8
    cc
    wcel
    @3
    @30
    adantr
    #
    imcld
    #
    @39
    readdcld
    #
    @20
    @22
    @36
    clt
    wbr
    #
    @36
    cc0
    clt
    wbr
    #
    @20
    @36
    @22
    cc0
    cioo
    co
    wcel
    #
    @43
    @44
    wa
    @20
    @31
    @9
    cim
    cfv
    #
    cc0
    clt
    wbr
    @45
    @0
    @31
    @3
    @32
    adantr
    @20
    @46
    @1
    cneg
    #
    cc0
    clt
    @20
    c1
    cim
    cfv
    #
    @6
    cim
    cfv
    #
    cmin
    co
    #
    @49
    cneg
    #
    @46
    @47
    @50
    cc0
    @49
    cmin
    co
    @51
    @48
    cc0
    @49
    cmin
    im1
    oveq1i
    @49
    df-neg
    eqtr4i
    @20
    @24
    @25
    @46
    @50
    wceq
    ax-1cn
    @0
    @25
    @3
    @27
    adantr
    #
    c1
    @6
    imsub
    sylancr
    @20
    @1
    @49
    @20
    @14
    @1
    @49
    wceq
    #
    @0
    @14
    @3
    @18
    adantr
    #
    cA
    reim
    #
    syl
    #
    negeqd
    3eqtr4a
    @0
    @3
    @47
    cc0
    clt
    wbr
    @0
    @1
    @19
    lt0neg2d
    biimpa
    eqbrtrd
    @9
    argimlt0
    syl2anc
    @36
    @22
    cc0
    eliooord
    syl
    #
    simpld
    @20
    cc0
    @35
    clt
    wbr
    #
    @36
    @37
    clt
    wbr
    @20
    @58
    @35
    cpi
    clt
    wbr
    #
    @20
    @35
    cc0
    cpi
    cioo
    co
    wcel
    #
    @58
    @59
    wa
    @20
    @26
    cc0
    @7
    cim
    cfv
    #
    clt
    wbr
    @60
    @0
    @26
    @3
    @28
    adantr
    @20
    cc0
    @1
    @61
    clt
    @0
    @3
    simpr
    @20
    @61
    @48
    @49
    caddc
    co
    #
    @48
    @1
    caddc
    co
    #
    @1
    @20
    @24
    @25
    @61
    @62
    wceq
    ax-1cn
    @52
    c1
    @6
    imadd
    sylancr
    @20
    @1
    @49
    @48
    caddc
    @56
    oveq2d
    @20
    @63
    cc0
    @1
    caddc
    co
    @1
    @48
    cc0
    @1
    caddc
    im1
    oveq1i
    @20
    @1
    @20
    @1
    @20
    cA
    @54
    recld
    recnd
    addid2d
    syl5eq
    3eqtr2d
    breqtrrd
    @7
    argimgt0
    syl2anc
    @35
    cc0
    cpi
    eliooord
    syl
    #
    simpld
    @20
    @35
    @36
    @41
    @39
    ltaddpos2d
    mpbid
    lttrd
    @20
    @8
    @10
    @40
    @38
    imaddd
    #
    breqtrrd
    @20
    @23
    @37
    cpi
    cle
    @65
    @20
    @37
    cpi
    @42
    cpi
    cr
    wcel
    @20
    pire
    a1i
    #
    @20
    @37
    @35
    cpi
    @42
    @41
    @66
    @20
    @37
    @35
    cc0
    caddc
    co
    @35
    clt
    @20
    @36
    cc0
    @35
    @39
    @20
    0red
    @41
    @20
    @43
    @44
    @57
    simprd
    ltadd2dd
    @20
    @35
    @20
    @35
    @41
    recnd
    addid1d
    breqtrd
    @20
    @58
    @59
    @64
    simprd
    lttrd
    ltled
    eqbrtrd
    @11
    ellogrn
    syl3anbrc
    @0
    @4
    wa
    #
    @13
    cc0
    @6
    @67
    0red
    #
    @67
    @6
    @0
    @25
    @4
    @27
    adantr
    @67
    cc0
    @1
    @49
    @0
    @4
    simpr
    @67
    @14
    @53
    @0
    @14
    @4
    @18
    adantr
    @55
    syl
    eqtr2d
    reim0bd
    #
    @67
    cc0
    @6
    cle
    wbr
    #
    wa
    #
    @11
    @10
    @8
    caddc
    co
    #
    @12
    @0
    @11
    @72
    wceq
    @4
    @70
    @0
    @8
    @10
    @30
    @34
    addcomd
    ad2antrr
    @71
    @10
    @12
    wcel
    #
    @8
    cr
    wcel
    @72
    @12
    wcel
    @0
    @73
    @4
    @70
    @0
    @31
    @15
    @73
    @32
    @33
    @9
    logrncl
    syl2anc
    ad2antrr
    @71
    @7
    @71
    @7
    @71
    c1
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    1re
    @67
    @75
    @70
    @69
    adantr
    c1
    @6
    readdcl
    sylancr
    #
    @71
    cc0
    c1
    @7
    @71
    0red
    @71
    1red
    @76
    cc0
    c1
    clt
    wbr
    #
    @71
    0lt1
    a1i
    @67
    @70
    c1
    @7
    cle
    wbr
    #
    @67
    @74
    @75
    @70
    @78
    wb
    1re
    @69
    c1
    @6
    addge01
    sylancr
    biimpa
    ltletrd
    elrpd
    relogcld
    @10
    @8
    logrnaddcl
    syl2anc
    eqeltrd
    @67
    @6
    cc0
    cle
    wbr
    #
    wa
    #
    @8
    @12
    wcel
    #
    @10
    cr
    wcel
    @13
    @0
    @81
    @4
    @79
    @0
    @26
    @16
    @81
    @28
    @29
    @7
    logrncl
    syl2anc
    ad2antrr
    @80
    @9
    @80
    @9
    @80
    @74
    @75
    @9
    cr
    wcel
    1re
    @67
    @75
    @79
    @69
    adantr
    c1
    @6
    resubcl
    sylancr
    #
    @80
    cc0
    c1
    @9
    @80
    0red
    @80
    1red
    @82
    @77
    @80
    0lt1
    a1i
    @80
    c1
    c1
    cc0
    cmin
    co
    #
    @9
    cle
    1m0e1
    @67
    @79
    @83
    @9
    cle
    wbr
    @67
    @6
    cc0
    c1
    @69
    @68
    @67
    1red
    lesub2d
    biimpa
    syl5eqbrr
    ltletrd
    elrpd
    relogcld
    @8
    @10
    logrnaddcl
    syl2anc
    lecasei
    jaodan
    syldan
end
