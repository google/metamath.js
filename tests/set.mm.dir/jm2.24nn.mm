include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "crmy.mm"
include "caddc.mm"
include "cmul.mm"
include "crmx.mm"
include "cz.mm"
include "nnz.mm"
include "1z.mm"
include "zsubcl.mm"
include "sylancl.mm"
include "frmy.mm"
include "fovcl.mm"
include "sylan2.mm"
include "zred.mm"
include "readdcld.mm"
include "cr.mm"
include "2re.mm"
include "remulcl.mm"
include "sylancr.mm"
include "resubcld.mm"
include "cn0.mm"
include "frmx.mm"
include "nn0red.mm"
include "clt.mm"
include "wbr.mm"
include "eluzelre.mm"
include "adantr.mm"
include "remulcld.mm"
include "a1i.mm"
include "cc0.mm"
include "cle.mm"
include "nnm1nn0.mm"
include "rmxypos.mm"
include "simprd.mm"
include "eluzle.mm"
include "lemul1ad.mm"
include "recnd.mm"
include "mulcomd.mm"
include "simpld.mm"
include "ltaddposd.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "lelttrd.mm"
include "2timesd.mm"
include "wceq.mm"
include "rmyp1.mm"
include "cc.mm"
include "nnre.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "3brtr3d.mm"
include "ltaddsubd.mm"
include "ltadd1dd.mm"
include "oveq1d.mm"
include "addsubd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "wb.mm"
include "rmy0.mm"
include "nngt0.mm"
include "simpl.mm"
include "0zd.mm"
include "ltrmy.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "lesub1dd.mm"
include "rmym1.mm"
include "eqtr2d.mm"
include "subsub23.mm"
include "breqtrd.mm"
include "ltletrd.mm"

theorem jm2.24nn
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN ) -> ( ( A rmY ( N - 1 ) ) + ( A rmY N ) ) < ( A rmX N ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    cN
    c1
    cmin
    co
    #
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    caddc
    co
    #
    c2
    @6
    cmul
    co
    #
    @5
    cmin
    co
    #
    cA
    cN
    crmx
    co
    #
    @3
    @5
    @6
    @3
    @5
    @2
    @1
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    @2
    cN
    cz
    wcel
    #
    c1
    cz
    wcel
    @11
    cN
    nnz
    #
    1z
    cN
    c1
    zsubcl
    sylancl
    #
    cA
    @4
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    zred
    #
    @3
    @6
    @2
    @1
    @12
    @6
    cz
    wcel
    @13
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    zred
    #
    readdcld
    @3
    @8
    @5
    @3
    c2
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @8
    cr
    wcel
    2re
    @16
    c2
    @6
    remulcl
    sylancr
    #
    @15
    resubcld
    @3
    @10
    @2
    @1
    @12
    @10
    cn0
    wcel
    @13
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    nn0red
    #
    @3
    @7
    @6
    @5
    cmin
    co
    #
    @6
    caddc
    co
    #
    @9
    clt
    @3
    @5
    @21
    @6
    @15
    @3
    @6
    @5
    @16
    @15
    resubcld
    @16
    @3
    @5
    @5
    caddc
    co
    #
    @6
    clt
    wbr
    @5
    @21
    clt
    wbr
    @3
    c2
    @5
    cmul
    co
    #
    @5
    cA
    cmul
    co
    #
    cA
    @4
    crmx
    co
    #
    caddc
    co
    #
    @23
    @6
    clt
    @3
    @24
    cA
    @5
    cmul
    co
    #
    @27
    @3
    @17
    @5
    cr
    wcel
    @24
    cr
    wcel
    2re
    @15
    c2
    @5
    remulcl
    sylancr
    @3
    cA
    @5
    @1
    cA
    cr
    wcel
    #
    @2
    c2
    cA
    eluzelre
    adantr
    #
    @15
    remulcld
    @3
    @25
    @26
    @3
    @5
    cA
    @15
    @30
    remulcld
    #
    @3
    @26
    @2
    @1
    @11
    @26
    cn0
    wcel
    @14
    cA
    @4
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    nn0red
    #
    readdcld
    @3
    c2
    cA
    @5
    @17
    @3
    2re
    a1i
    #
    @30
    @15
    @2
    @1
    @4
    cn0
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    cN
    nnm1nn0
    #
    @1
    @34
    wa
    #
    cc0
    @26
    clt
    wbr
    #
    @35
    cA
    @4
    rmxypos
    #
    simprd
    sylan2
    @1
    c2
    cA
    cle
    wbr
    #
    @2
    c2
    cA
    eluzle
    adantr
    #
    lemul1ad
    @3
    @28
    @25
    @27
    clt
    @3
    cA
    @5
    @3
    cA
    @30
    recnd
    #
    @3
    @5
    @15
    recnd
    #
    mulcomd
    @3
    @38
    @25
    @27
    clt
    wbr
    @2
    @1
    @34
    @38
    @36
    @37
    @38
    @35
    @39
    simpld
    sylan2
    @3
    @26
    @25
    @32
    @31
    ltaddposd
    mpbid
    eqbrtrd
    lelttrd
    @3
    @5
    @43
    2timesd
    @3
    cA
    @4
    c1
    caddc
    co
    #
    crmy
    co
    #
    @27
    @6
    @2
    @1
    @11
    @45
    @27
    wceq
    @14
    cA
    @4
    rmyp1
    sylan2
    @3
    @44
    cN
    cA
    crmy
    @3
    cN
    cc
    wcel
    c1
    cc
    wcel
    @44
    cN
    wceq
    @3
    cN
    @2
    cN
    cr
    wcel
    @1
    cN
    nnre
    adantl
    recnd
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq2d
    eqtr3d
    3brtr3d
    @3
    @5
    @5
    @6
    @15
    @15
    @16
    ltaddsubd
    mpbid
    ltadd1dd
    @3
    @9
    @6
    @6
    caddc
    co
    #
    @5
    cmin
    co
    @22
    @3
    @8
    @46
    @5
    cmin
    @3
    @6
    @3
    @6
    @16
    recnd
    #
    2timesd
    oveq1d
    @3
    @6
    @6
    @5
    @47
    @47
    @43
    addsubd
    eqtrd
    breqtrrd
    @3
    @9
    cA
    @6
    cmul
    co
    #
    @5
    cmin
    co
    #
    @10
    cle
    @3
    @8
    @48
    @5
    @19
    @3
    cA
    @6
    @30
    @16
    remulcld
    #
    @15
    @3
    @40
    @8
    @48
    cle
    wbr
    #
    @41
    @3
    @17
    @29
    @18
    cc0
    @6
    clt
    wbr
    @40
    @51
    wb
    @33
    @30
    @16
    @3
    cA
    cc0
    crmy
    co
    #
    cc0
    @6
    clt
    @1
    @52
    cc0
    wceq
    @2
    cA
    rmy0
    adantr
    @3
    cc0
    cN
    clt
    wbr
    #
    @52
    @6
    clt
    wbr
    #
    @2
    @53
    @1
    cN
    nngt0
    adantl
    @3
    @1
    cc0
    cz
    wcel
    @12
    @53
    @54
    wb
    @1
    @2
    simpl
    @3
    0zd
    @2
    @12
    @1
    @13
    adantl
    cA
    cc0
    cN
    ltrmy
    syl3anc
    mpbid
    eqbrtrrd
    c2
    cA
    @6
    lemul1
    syl112anc
    mpbid
    lesub1dd
    @3
    @48
    @10
    cmin
    co
    #
    @5
    wceq
    #
    @49
    @10
    wceq
    #
    @3
    @5
    @6
    cA
    cmul
    co
    #
    @10
    cmin
    co
    #
    @55
    @2
    @1
    @12
    @5
    @59
    wceq
    @13
    cA
    cN
    rmym1
    sylan2
    @3
    @58
    @48
    @10
    cmin
    @3
    @6
    cA
    @47
    @42
    mulcomd
    oveq1d
    eqtr2d
    @3
    @48
    cc
    wcel
    @10
    cc
    wcel
    @5
    cc
    wcel
    @56
    @57
    wb
    @3
    @48
    @50
    recnd
    @3
    @10
    @20
    recnd
    @43
    @48
    @10
    @5
    subsub23
    syl3anc
    mpbid
    breqtrd
    ltletrd
end
