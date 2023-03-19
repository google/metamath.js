include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crmy.mm"
include "cmul.mm"
include "cexp.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "1le1.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "rmy1.mm"
include "syl5eq.mm"
include "cr.mm"
include "2re.mm"
include "eluzelre.mm"
include "remulcl.mm"
include "sylancr.mm"
include "recnd.mm"
include "exp0d.mm"
include "mpbiri.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "cz.mm"
include "simpr.mm"
include "nn0z.mm"
include "adantr.mm"
include "peano2zd.mm"
include "rmyluc2.mm"
include "syl2anc.mm"
include "crmx.mm"
include "clt.mm"
include "rmxypos.mm"
include "simprd.mm"
include "ancoms.mm"
include "cc.mm"
include "nn0re.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "breqtrrd.mm"
include "adantl.mm"
include "frmy.mm"
include "fovcl.mm"
include "zred.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "subge02d.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "3adant3.mm"
include "wb.mm"
include "simpl.mm"
include "reexpcld.mm"
include "cn.mm"
include "2nn.mm"
include "eluz2nn.mm"
include "nnmulcl.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "biimp3a.mm"
include "expp1d.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "peano2nn0.mm"
include "letr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem jm2.17b
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A rmY ( N + 1 ) ) <_ ( ( 2 x. A ) ^ N ) )

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
    cA
    cN
    c1
    caddc
    co
    #
    crmy
    co
    #
    c2
    cA
    cmul
    co
    #
    cN
    cexp
    co
    #
    cle
    wbr
    #
    @1
    cA
    va
    cv
    #
    c1
    caddc
    co
    #
    crmy
    co
    #
    @4
    @7
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @1
    cA
    cc0
    c1
    caddc
    co
    #
    crmy
    co
    #
    @4
    cc0
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @1
    cA
    vb
    cv
    #
    c1
    caddc
    co
    #
    crmy
    co
    #
    @4
    @16
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @1
    cA
    @17
    c1
    caddc
    co
    #
    crmy
    co
    #
    @4
    @17
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @1
    @6
    wi
    va
    vb
    cN
    @7
    cc0
    wceq
    #
    @11
    @15
    @1
    @25
    @9
    @13
    @10
    @14
    cle
    @25
    @8
    @12
    cA
    crmy
    @7
    cc0
    c1
    caddc
    oveq1
    oveq2d
    @7
    cc0
    @4
    cexp
    oveq2
    breq12d
    imbi2d
    va
    vb
    weq
    #
    @11
    @20
    @1
    @26
    @9
    @18
    @10
    @19
    cle
    @26
    @8
    @17
    cA
    crmy
    @7
    @16
    c1
    caddc
    oveq1
    oveq2d
    @7
    @16
    @4
    cexp
    oveq2
    breq12d
    imbi2d
    @7
    @17
    wceq
    #
    @11
    @24
    @1
    @27
    @9
    @22
    @10
    @23
    cle
    @27
    @8
    @21
    cA
    crmy
    @7
    @17
    c1
    caddc
    oveq1
    oveq2d
    @7
    @17
    @4
    cexp
    oveq2
    breq12d
    imbi2d
    @7
    cN
    wceq
    #
    @11
    @6
    @1
    @28
    @9
    @3
    @10
    @5
    cle
    @28
    @8
    @2
    cA
    crmy
    @7
    cN
    c1
    caddc
    oveq1
    oveq2d
    @7
    cN
    @4
    cexp
    oveq2
    breq12d
    imbi2d
    @1
    @15
    c1
    c1
    cle
    wbr
    1le1
    @1
    @13
    c1
    @14
    c1
    cle
    @1
    @13
    cA
    c1
    crmy
    co
    c1
    @12
    c1
    cA
    crmy
    0p1e1
    oveq2i
    cA
    rmy1
    syl5eq
    @1
    @4
    @1
    @4
    @1
    c2
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    2re
    c2
    cA
    eluzelre
    #
    c2
    cA
    remulcl
    #
    sylancr
    recnd
    exp0d
    breq12d
    mpbiri
    @16
    cn0
    wcel
    #
    @1
    @20
    @24
    @34
    @1
    @20
    @24
    @34
    @1
    @20
    w3a
    #
    @22
    @4
    @18
    cmul
    co
    #
    cle
    wbr
    #
    @36
    @23
    cle
    wbr
    #
    @24
    @34
    @1
    @37
    @20
    @34
    @1
    wa
    #
    @22
    @36
    cA
    @17
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
    cle
    @39
    @1
    @17
    cz
    wcel
    #
    @22
    @42
    wceq
    @34
    @1
    simpr
    #
    @39
    @16
    @34
    @16
    cz
    wcel
    #
    @1
    @16
    nn0z
    adantr
    #
    peano2zd
    #
    cA
    @17
    rmyluc2
    syl2anc
    @39
    cc0
    @41
    cle
    wbr
    @42
    @36
    cle
    wbr
    @39
    cc0
    cA
    @16
    crmy
    co
    #
    @41
    cle
    @1
    @34
    cc0
    @48
    cle
    wbr
    #
    @1
    @34
    wa
    cc0
    cA
    @16
    crmx
    co
    clt
    wbr
    @49
    cA
    @16
    rmxypos
    simprd
    ancoms
    @39
    @40
    @16
    cA
    crmy
    @39
    @16
    cc
    wcel
    c1
    cc
    wcel
    @40
    @16
    wceq
    @39
    @16
    @34
    @16
    cr
    wcel
    @1
    @16
    nn0re
    adantr
    recnd
    ax-1cn
    @16
    c1
    pncan
    sylancl
    oveq2d
    #
    breqtrrd
    @39
    @36
    @41
    @39
    @4
    @18
    @39
    @29
    @30
    @31
    2re
    @1
    @30
    @34
    @32
    adantl
    @33
    sylancr
    #
    @39
    @1
    @43
    @18
    cr
    wcel
    #
    @44
    @47
    @1
    @43
    wa
    @18
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
    #
    remulcld
    #
    @39
    @41
    @48
    cr
    @50
    @39
    @1
    @45
    @48
    cr
    wcel
    @44
    @46
    @1
    @45
    wa
    @48
    cA
    @16
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    syl2anc
    eqeltrd
    subge02d
    mpbid
    eqbrtrd
    3adant3
    @35
    @36
    @4
    @19
    cmul
    co
    #
    @23
    cle
    @34
    @1
    @20
    @36
    @55
    cle
    wbr
    #
    @39
    @52
    @19
    cr
    wcel
    @31
    cc0
    @4
    clt
    wbr
    #
    @20
    @56
    wb
    @53
    @39
    @4
    @16
    @51
    @34
    @1
    simpl
    #
    reexpcld
    #
    @51
    @1
    @57
    @34
    @1
    @4
    @1
    c2
    cn
    wcel
    cA
    cn
    wcel
    @4
    cn
    wcel
    2nn
    cA
    eluz2nn
    c2
    cA
    nnmulcl
    sylancr
    nngt0d
    adantl
    @18
    @19
    @4
    lemul2
    syl112anc
    biimp3a
    @34
    @1
    @23
    @55
    wceq
    @20
    @39
    @23
    @19
    @4
    cmul
    co
    @55
    @39
    @4
    @16
    @39
    @4
    @51
    recnd
    #
    @58
    expp1d
    @39
    @19
    @4
    @39
    @19
    @59
    recnd
    @60
    mulcomd
    eqtrd
    3adant3
    breqtrrd
    @34
    @1
    @37
    @38
    wa
    @24
    wi
    #
    @20
    @39
    @22
    cr
    wcel
    #
    @36
    cr
    wcel
    @23
    cr
    wcel
    @61
    @39
    @1
    @21
    cz
    wcel
    #
    @62
    @44
    @39
    @17
    @47
    peano2zd
    @1
    @63
    wa
    @22
    cA
    @21
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    syl2anc
    @54
    @39
    @4
    @17
    @51
    @34
    @17
    cn0
    wcel
    @1
    @16
    peano2nn0
    adantr
    reexpcld
    @22
    @36
    @23
    letr
    syl3anc
    3adant3
    mp2and
    3exp
    a2d
    nn0ind
    impcom
end
