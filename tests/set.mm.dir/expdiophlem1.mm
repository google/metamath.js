include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "crmy.mm"
include "crmx.mm"
include "cmul.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cdvds.mm"
include "wrex.mm"
include "cmo.mm"
include "cle.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nnre.mm"
include "peano2re.mm"
include "syl.mm"
include "adantl.mm"
include "cz.mm"
include "nnz.mm"
include "peano2zd.mm"
include "frmy.mm"
include "fovcl.mm"
include "sylan2.mm"
include "zred.mm"
include "elnnuz.mm"
include "eluzp1p1.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "sylbi.mm"
include "eluzle.mm"
include "nnnn0.mm"
include "peano2nn0.mm"
include "rmygeid.mm"
include "letrd.mm"
include "wb.mm"
include "2z.mm"
include "eluz.mm"
include "sylancr.mm"
include "mpbird.mm"
include "simprl.mm"
include "simprr.mm"
include "leidd.mm"
include "jm3.1.mm"
include "syl31anc.mm"
include "eqeq2d.mm"
include "frmx.mm"
include "syl2anc.mm"
include "nn0zd.mm"
include "eluzelz.mm"
include "adantr.mm"
include "zsubcld.mm"
include "zmulcld.mm"
include "jm3.1lem3.mm"
include "simpl.mm"
include "divalgmodcl.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "rmynn0.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "ceqsrexv.mm"
include "ad2antll.mm"
include "anbi2d.mm"
include "3bitrrd.mm"
include "r19.42v.mm"
include "anbi2i.mm"
include "bitri.mm"
include "rexbii.mm"
include "syl6bbr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "ibar.mm"
include "anbi1d.mm"
include "pm5.32da.mm"
include "ad2antrl.mm"
include "2rexbidv.mm"
include "2rexbii.mm"

theorem expdiophlem1
  let cA: class A
  let cB: class B
  let cC: class C
  let ve: setvar e
  let vf: setvar f
  let vd: setvar d

  disjoint A d
  disjoint A e
  disjoint A f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint C d
  disjoint C e
  disjoint C f
  assert |- ( C e. NN0 -> ( ( ( A e. ( ZZ>= ` 2 ) /\ B e. NN ) /\ C = ( A ^ B ) ) <-> E. d e. NN0 E. e e. NN0 E. f e. NN0 ( ( A e. ( ZZ>= ` 2 ) /\ B e. NN ) /\ ( ( A e. ( ZZ>= ` 2 ) /\ d = ( A rmY ( B + 1 ) ) ) /\ ( ( d e. ( ZZ>= ` 2 ) /\ e = ( d rmY B ) ) /\ ( ( d e. ( ZZ>= ` 2 ) /\ f = ( d rmX B ) ) /\ ( C < ( ( ( ( 2 x. d ) x. A ) - ( A ^ 2 ) ) - 1 ) /\ ( ( ( ( 2 x. d ) x. A ) - ( A ^ 2 ) ) - 1 ) || ( ( f - ( ( d - A ) x. e ) ) - C ) ) ) ) ) ) ) )

  proof
    cC
    cn0
    wcel
    #
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cexp
    co
    #
    wceq
    #
    wa
    @4
    @2
    vd
    cv
    #
    cA
    cB
    c1
    caddc
    co
    #
    crmy
    co
    #
    wceq
    #
    wa
    #
    @7
    @1
    wcel
    #
    ve
    cv
    #
    @7
    cB
    crmy
    co
    #
    wceq
    #
    wa
    #
    @12
    vf
    cv
    #
    @7
    cB
    crmx
    co
    #
    wceq
    #
    wa
    #
    cC
    c2
    @7
    cmul
    co
    #
    cA
    cmul
    co
    #
    cA
    c2
    cexp
    co
    #
    cmin
    co
    #
    c1
    cmin
    co
    #
    clt
    wbr
    #
    @25
    @17
    @7
    cA
    cmin
    co
    #
    @13
    cmul
    co
    #
    cmin
    co
    #
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    wa
    #
    wa
    #
    vf
    cn0
    wrex
    #
    ve
    cn0
    wrex
    #
    vd
    cn0
    wrex
    #
    wa
    #
    @4
    @35
    wa
    vf
    cn0
    wrex
    #
    ve
    cn0
    wrex
    vd
    cn0
    wrex
    #
    @0
    @4
    @6
    @38
    @0
    @4
    wa
    #
    @6
    cC
    c2
    @9
    cmul
    co
    #
    cA
    cmul
    co
    #
    @23
    cmin
    co
    #
    c1
    cmin
    co
    #
    clt
    wbr
    #
    @46
    @9
    cB
    crmx
    co
    #
    @9
    cA
    cmin
    co
    #
    @9
    cB
    crmy
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @38
    @42
    @6
    cC
    @52
    @46
    cmo
    co
    #
    wceq
    #
    @55
    @42
    @5
    @56
    cC
    @42
    @9
    @1
    wcel
    #
    @2
    @3
    @9
    @9
    cle
    wbr
    #
    @5
    @56
    wceq
    @4
    @58
    @0
    @4
    @58
    c2
    @9
    cle
    wbr
    #
    @4
    c2
    @8
    @9
    c2
    cr
    wcel
    @4
    2re
    a1i
    @3
    @8
    cr
    wcel
    #
    @2
    @3
    cB
    cr
    wcel
    @61
    cB
    nnre
    cB
    peano2re
    syl
    adantl
    @4
    @9
    @3
    @2
    @8
    cz
    wcel
    @9
    cz
    wcel
    #
    @3
    cB
    cB
    nnz
    #
    peano2zd
    cA
    @8
    cz
    @1
    cz
    crmy
    frmy
    fovcl
    sylan2
    #
    zred
    #
    @3
    c2
    @8
    cle
    wbr
    #
    @2
    @3
    @8
    @1
    wcel
    #
    @66
    @3
    cB
    c1
    cuz
    cfv
    wcel
    #
    @67
    cB
    elnnuz
    @68
    @8
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    @1
    c1
    cB
    eluzp1p1
    c2
    @69
    cuz
    df-2
    fveq2i
    syl6eleqr
    sylbi
    c2
    @8
    eluzle
    syl
    adantl
    @3
    @2
    @8
    cn0
    wcel
    #
    @8
    @9
    cle
    wbr
    @3
    cB
    cn0
    wcel
    #
    @70
    cB
    nnnn0
    #
    cB
    peano2nn0
    syl
    #
    cA
    @8
    rmygeid
    sylan2
    letrd
    @4
    c2
    cz
    wcel
    @62
    @58
    @60
    wb
    2z
    @64
    c2
    @9
    eluz
    sylancr
    mpbird
    #
    adantl
    #
    @0
    @2
    @3
    simprl
    #
    @0
    @2
    @3
    simprr
    #
    @4
    @59
    @0
    @4
    @9
    @65
    leidd
    adantl
    #
    @9
    cA
    cB
    jm3.1
    syl31anc
    eqeq2d
    @42
    @52
    cz
    wcel
    #
    @46
    cn
    wcel
    @0
    @57
    @55
    wb
    @4
    @79
    @0
    @4
    @48
    @51
    @4
    @48
    @4
    @58
    cB
    cz
    wcel
    #
    @48
    cn0
    wcel
    #
    @74
    @3
    @80
    @2
    @63
    adantl
    #
    @9
    cB
    cn0
    @1
    cz
    crmx
    frmx
    fovcl
    #
    syl2anc
    nn0zd
    @4
    @49
    @50
    @4
    @9
    cA
    @64
    @2
    cA
    cz
    wcel
    @3
    c2
    cA
    eluzelz
    adantr
    zsubcld
    @4
    @58
    @80
    @50
    cz
    wcel
    @74
    @82
    @9
    cB
    cz
    @1
    cz
    crmy
    frmy
    fovcl
    syl2anc
    zmulcld
    zsubcld
    adantl
    @42
    @9
    cA
    cB
    @75
    @76
    @77
    @78
    jm3.1lem3
    @0
    @4
    simpl
    @46
    cC
    @52
    divalgmodcl
    syl3anc
    bitrd
    @42
    @55
    @10
    @15
    @19
    @32
    wa
    #
    wa
    #
    wa
    #
    vf
    cn0
    wrex
    #
    ve
    cn0
    wrex
    #
    vd
    cn0
    wrex
    #
    @38
    @42
    @55
    @10
    @15
    @84
    vf
    cn0
    wrex
    #
    wa
    #
    ve
    cn0
    wrex
    #
    wa
    #
    vd
    cn0
    wrex
    #
    @89
    @42
    @94
    @13
    @50
    wceq
    #
    @17
    @48
    wceq
    #
    @47
    @46
    @17
    @49
    @13
    cmul
    co
    #
    cmin
    co
    #
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    vf
    cn0
    wrex
    #
    wa
    #
    ve
    cn0
    wrex
    #
    @96
    @47
    @46
    @17
    @51
    cmin
    co
    #
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    vf
    cn0
    wrex
    #
    @55
    @42
    @9
    cn0
    wcel
    #
    @94
    @105
    wb
    @4
    @112
    @0
    @3
    @2
    @70
    @112
    @73
    cA
    @8
    rmynn0
    sylan2
    adantl
    @92
    @105
    vd
    @9
    cn0
    @10
    @91
    @104
    ve
    cn0
    @10
    @15
    @95
    @90
    @103
    @10
    @14
    @50
    @13
    @7
    @9
    cB
    crmy
    oveq1
    eqeq2d
    @10
    @84
    @102
    vf
    cn0
    @10
    @19
    @96
    @32
    @101
    @10
    @18
    @48
    @17
    @7
    @9
    cB
    crmx
    oveq1
    eqeq2d
    @10
    @26
    @47
    @31
    @100
    @10
    @25
    @46
    cC
    clt
    @10
    @24
    @45
    c1
    cmin
    @10
    @22
    @44
    @23
    cmin
    @10
    @21
    @43
    cA
    cmul
    @7
    @9
    c2
    cmul
    oveq2
    oveq1d
    oveq1d
    oveq1d
    #
    breq2d
    @10
    @25
    @46
    @30
    @99
    cdvds
    @113
    @10
    @29
    @98
    cC
    cmin
    @10
    @28
    @97
    @17
    cmin
    @10
    @27
    @49
    @13
    cmul
    @7
    @9
    cA
    cmin
    oveq1
    oveq1d
    oveq2d
    oveq1d
    breq12d
    anbi12d
    anbi12d
    rexbidv
    anbi12d
    rexbidv
    ceqsrexv
    syl
    @42
    @50
    cn0
    wcel
    #
    @105
    @111
    wb
    @42
    @58
    @71
    @114
    @75
    @3
    @71
    @0
    @2
    @72
    ad2antll
    @9
    cB
    rmynn0
    syl2anc
    @103
    @111
    ve
    @50
    cn0
    @95
    @102
    @110
    vf
    cn0
    @95
    @101
    @109
    @96
    @95
    @100
    @108
    @47
    @95
    @99
    @107
    @46
    cdvds
    @95
    @98
    @106
    cC
    cmin
    @95
    @97
    @51
    @17
    cmin
    @13
    @50
    @49
    cmul
    oveq2
    oveq2d
    oveq1d
    breq2d
    anbi2d
    anbi2d
    rexbidv
    ceqsrexv
    syl
    @42
    @81
    @111
    @55
    wb
    @42
    @58
    @80
    @81
    @75
    @3
    @80
    @0
    @2
    @63
    ad2antll
    @83
    syl2anc
    @109
    @55
    vf
    @48
    cn0
    @96
    @108
    @54
    @47
    @96
    @107
    @53
    @46
    cdvds
    @96
    @106
    @52
    cC
    cmin
    @17
    @48
    @51
    cmin
    oveq1
    oveq1d
    breq2d
    anbi2d
    ceqsrexv
    syl
    3bitrrd
    @88
    @93
    vd
    cn0
    @88
    @10
    @91
    wa
    #
    ve
    cn0
    wrex
    @93
    @87
    @115
    ve
    cn0
    @87
    @10
    @85
    vf
    cn0
    wrex
    #
    wa
    @115
    @10
    @85
    vf
    cn0
    r19.42v
    @116
    @91
    @10
    @15
    @84
    vf
    cn0
    r19.42v
    anbi2i
    bitri
    rexbii
    @10
    @91
    ve
    cn0
    r19.42v
    bitri
    rexbii
    syl6bbr
    @42
    @87
    @36
    vd
    ve
    cn0
    cn0
    @42
    @86
    @35
    vf
    cn0
    @42
    @86
    @10
    @34
    wa
    @35
    @42
    @10
    @85
    @34
    @42
    @10
    wa
    @12
    @85
    @34
    wb
    @42
    @10
    @12
    @42
    @12
    @10
    @58
    @75
    @7
    @9
    @1
    eleq1
    syl5ibrcom
    imp
    @12
    @15
    @16
    @84
    @33
    @12
    @15
    ibar
    @12
    @19
    @20
    @32
    @12
    @19
    ibar
    anbi1d
    anbi12d
    syl
    pm5.32da
    @42
    @10
    @11
    @34
    @2
    @10
    @11
    wb
    @0
    @3
    @2
    @10
    ibar
    ad2antrl
    anbi1d
    bitrd
    rexbidv
    2rexbidv
    bitrd
    bitrd
    pm5.32da
    @41
    @4
    @36
    wa
    #
    ve
    cn0
    wrex
    #
    vd
    cn0
    wrex
    #
    @39
    @40
    @117
    vd
    ve
    cn0
    cn0
    @4
    @35
    vf
    cn0
    r19.42v
    2rexbii
    @119
    @4
    @37
    wa
    #
    vd
    cn0
    wrex
    @39
    @118
    @120
    vd
    cn0
    @4
    @36
    ve
    cn0
    r19.42v
    rexbii
    @4
    @37
    vd
    cn0
    r19.42v
    bitri
    bitri
    syl6bbr
end
