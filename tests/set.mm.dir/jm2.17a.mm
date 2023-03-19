include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cexp.mm"
include "caddc.mm"
include "crmy.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "1le1.mm"
include "a1i.mm"
include "cc.mm"
include "2cn.mm"
include "eluzelcn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "exp0d.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "rmy1.mm"
include "syl5eq.mm"
include "3brtr4d.mm"
include "w3a.mm"
include "cr.mm"
include "wa.mm"
include "2re.mm"
include "eluzelre.mm"
include "adantl.mm"
include "remulcl.mm"
include "1re.mm"
include "resubcl.mm"
include "peano2nn0.mm"
include "adantr.mm"
include "reexpcld.mm"
include "3adant3.mm"
include "cz.mm"
include "simpr.mm"
include "nn0z.mm"
include "peano2zd.mm"
include "frmy.mm"
include "fovcl.mm"
include "zred.mm"
include "syl2anc.mm"
include "remulcld.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "expp1d.mm"
include "simpl.mm"
include "cn.mm"
include "2nn.mm"
include "eluz2nn.mm"
include "nnmulcl.mm"
include "nnm1nn0.mm"
include "nn0ge0.mm"
include "3syl.mm"
include "jca.mm"
include "3jca.mm"
include "lemul1a.mm"
include "stoic3.mm"
include "eqbrtrd.mm"
include "nn0cn.mm"
include "pncan.mm"
include "eqeltrd.mm"
include "nn0re.mm"
include "lep1d.mm"
include "wb.mm"
include "lermy.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "recnd.mm"
include "mulid1d.mm"
include "lesub2dd.mm"
include "subdid.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "rmyluc2.mm"
include "letrd.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem jm2.17a
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( ( ( 2 x. A ) - 1 ) ^ N ) <_ ( A rmY ( N + 1 ) ) )

  proof
    cN
    cn0
    wcel
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    c2
    cA
    cmul
    co
    #
    c1
    cmin
    co
    #
    cN
    cexp
    co
    #
    cA
    cN
    c1
    caddc
    co
    #
    crmy
    co
    #
    cle
    wbr
    #
    @1
    @3
    va
    cv
    #
    cexp
    co
    #
    cA
    @8
    c1
    caddc
    co
    #
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    @3
    cc0
    cexp
    co
    #
    cA
    cc0
    c1
    caddc
    co
    #
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    @3
    vb
    cv
    #
    cexp
    co
    #
    cA
    @17
    c1
    caddc
    co
    #
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    @3
    @19
    cexp
    co
    #
    cA
    @19
    c1
    caddc
    co
    #
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    @7
    wi
    va
    vb
    cN
    @8
    cc0
    wceq
    #
    @12
    @16
    @1
    @26
    @9
    @13
    @11
    @15
    cle
    @8
    cc0
    @3
    cexp
    oveq2
    @26
    @10
    @14
    cA
    crmy
    @8
    cc0
    c1
    caddc
    oveq1
    oveq2d
    breq12d
    imbi2d
    va
    vb
    weq
    #
    @12
    @21
    @1
    @27
    @9
    @18
    @11
    @20
    cle
    @8
    @17
    @3
    cexp
    oveq2
    @27
    @10
    @19
    cA
    crmy
    @8
    @17
    c1
    caddc
    oveq1
    oveq2d
    breq12d
    imbi2d
    @8
    @19
    wceq
    #
    @12
    @25
    @1
    @28
    @9
    @22
    @11
    @24
    cle
    @8
    @19
    @3
    cexp
    oveq2
    @28
    @10
    @23
    cA
    crmy
    @8
    @19
    c1
    caddc
    oveq1
    oveq2d
    breq12d
    imbi2d
    @8
    cN
    wceq
    #
    @12
    @7
    @1
    @29
    @9
    @4
    @11
    @6
    cle
    @8
    cN
    @3
    cexp
    oveq2
    @29
    @10
    @5
    cA
    crmy
    @8
    cN
    c1
    caddc
    oveq1
    oveq2d
    breq12d
    imbi2d
    @1
    c1
    c1
    @13
    @15
    cle
    c1
    c1
    cle
    wbr
    @1
    1le1
    a1i
    @1
    @3
    @1
    @2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @1
    c2
    cc
    wcel
    cA
    cc
    wcel
    @30
    2cn
    c2
    cA
    eluzelcn
    c2
    cA
    mulcl
    sylancr
    ax-1cn
    @2
    c1
    subcl
    sylancl
    #
    exp0d
    @1
    @15
    cA
    c1
    crmy
    co
    c1
    @14
    c1
    cA
    crmy
    0p1e1
    oveq2i
    cA
    rmy1
    syl5eq
    3brtr4d
    @17
    cn0
    wcel
    #
    @1
    @21
    @25
    @34
    @1
    @21
    @25
    @34
    @1
    @21
    w3a
    #
    @22
    @20
    @3
    cmul
    co
    #
    @24
    @34
    @1
    @22
    cr
    wcel
    @21
    @34
    @1
    wa
    #
    @3
    @19
    @37
    @2
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @37
    c2
    cr
    wcel
    cA
    cr
    wcel
    #
    @38
    2re
    @1
    @41
    @34
    c2
    cA
    eluzelre
    adantl
    c2
    cA
    remulcl
    sylancr
    #
    1re
    @2
    c1
    resubcl
    sylancl
    #
    @34
    @19
    cn0
    wcel
    @1
    @17
    peano2nn0
    adantr
    reexpcld
    3adant3
    @34
    @1
    @36
    cr
    wcel
    @21
    @37
    @20
    @3
    @37
    @1
    @19
    cz
    wcel
    #
    @20
    cr
    wcel
    #
    @34
    @1
    simpr
    #
    @37
    @17
    @34
    @17
    cz
    wcel
    #
    @1
    @17
    nn0z
    adantr
    #
    peano2zd
    #
    @1
    @44
    wa
    @20
    cA
    @19
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    syl2anc
    #
    @43
    remulcld
    3adant3
    @34
    @1
    @24
    cr
    wcel
    #
    @21
    @37
    @1
    @23
    cz
    wcel
    #
    @51
    @46
    @37
    @19
    @49
    peano2zd
    @1
    @52
    wa
    @24
    cA
    @23
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    syl2anc
    3adant3
    @35
    @22
    @18
    @3
    cmul
    co
    #
    @36
    cle
    @35
    @3
    @17
    @1
    @34
    @32
    @21
    @33
    3ad2ant2
    @34
    @1
    @21
    simp1
    expp1d
    @34
    @1
    @18
    cr
    wcel
    #
    @45
    @40
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    w3a
    @21
    @53
    @36
    cle
    wbr
    @37
    @54
    @45
    @56
    @37
    @3
    @17
    @43
    @34
    @1
    simpl
    reexpcld
    @50
    @37
    @40
    @55
    @43
    @37
    @2
    cn
    wcel
    #
    @3
    cn0
    wcel
    @55
    @37
    c2
    cn
    wcel
    cA
    cn
    wcel
    #
    @57
    2nn
    @1
    @58
    @34
    cA
    eluz2nn
    adantl
    c2
    cA
    nnmulcl
    sylancr
    @2
    nnm1nn0
    @3
    nn0ge0
    3syl
    jca
    3jca
    @18
    @20
    @3
    lemul1a
    stoic3
    eqbrtrd
    @34
    @1
    @36
    @24
    cle
    wbr
    @21
    @37
    @2
    @20
    cmul
    co
    #
    @20
    c1
    cmul
    co
    #
    cmin
    co
    #
    @59
    cA
    @19
    c1
    cmin
    co
    #
    crmy
    co
    #
    cmin
    co
    #
    @36
    @24
    cle
    @37
    @63
    @60
    @59
    @37
    @63
    cA
    @17
    crmy
    co
    #
    cr
    @37
    @62
    @17
    cA
    crmy
    @37
    @17
    cc
    wcel
    #
    @31
    @62
    @17
    wceq
    @34
    @66
    @1
    @17
    nn0cn
    adantr
    ax-1cn
    @17
    c1
    pncan
    sylancl
    oveq2d
    #
    @37
    @1
    @47
    @65
    cr
    wcel
    @46
    @48
    @1
    @47
    wa
    @65
    cA
    @17
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    syl2anc
    eqeltrd
    @37
    @45
    @39
    @60
    cr
    wcel
    @50
    1re
    @20
    c1
    remulcl
    sylancl
    @37
    @2
    @20
    @42
    @50
    remulcld
    @37
    @65
    @20
    @63
    @60
    cle
    @37
    @17
    @19
    cle
    wbr
    #
    @65
    @20
    cle
    wbr
    #
    @37
    @17
    @34
    @17
    cr
    wcel
    @1
    @17
    nn0re
    adantr
    lep1d
    @37
    @1
    @47
    @44
    @68
    @69
    wb
    @46
    @48
    @49
    cA
    @17
    @19
    lermy
    syl3anc
    mpbid
    @67
    @37
    @20
    @37
    @20
    @50
    recnd
    #
    mulid1d
    3brtr4d
    lesub2dd
    @37
    @36
    @20
    @2
    cmul
    co
    #
    @60
    cmin
    co
    @61
    @37
    @20
    @2
    c1
    @70
    @37
    @2
    @42
    recnd
    #
    @31
    @37
    ax-1cn
    a1i
    subdid
    @37
    @71
    @59
    @60
    cmin
    @37
    @20
    @2
    @70
    @72
    mulcomd
    oveq1d
    eqtrd
    @37
    @1
    @44
    @24
    @64
    wceq
    @46
    @49
    cA
    @19
    rmyluc2
    syl2anc
    3brtr4d
    3adant3
    letrd
    3exp
    a2d
    nn0ind
    impcom
end
