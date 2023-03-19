include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cmin.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "eluzelre.mm"
include "syl.mm"
include "nnnn0d.mm"
include "reexpcld.mm"
include "2re.mm"
include "remulcl.mm"
include "sylancr.mm"
include "remulcld.mm"
include "resqcld.mm"
include "resubcld.mm"
include "1re.mm"
include "resubcl.mm"
include "sylancl.mm"
include "jm3.1lem1.mm"
include "caddc.mm"
include "readdcld.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "eluz2b1.mm"
include "simprbi.mm"
include "cc0.mm"
include "wb.mm"
include "cn.mm"
include "eluz2nn.mm"
include "nngt0d.mm"
include "ltmulgt11.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "uz2m1nn.mm"
include "nnrpd.mm"
include "ltaddrpd.mm"
include "lttrd.mm"
include "cle.mm"
include "peano2re.mm"
include "recnd.mm"
include "exp1d.mm"
include "nnge1d.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "leexp2ad.mm"
include "eqbrtrrd.mm"
include "lelttrd.mm"
include "eluzelz.mm"
include "zltp1le.mm"
include "syl2anc.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "leadd1dd.mm"
include "1cnd.mm"
include "addsub12d.mm"
include "adddird.mm"
include "sqvald.mm"
include "oveq12d.mm"
include "mulcld.mm"
include "cc.mm"
include "ax-1cn.mm"
include "mulcl.mm"
include "pncan2d.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "subadd23d.mm"
include "3eqtr3d.mm"
include "2cnd.mm"
include "mulassd.mm"
include "2timesd.mm"
include "eqtrd.mm"
include "sub32d.mm"
include "addsubassd.mm"
include "3brtr4d.mm"
include "ltletrd.mm"

theorem jm3.1lem2
  let wph: wff ph
  let cA: class A
  let cK: class K
  let cN: class N
  assume jm3.1.a: |- ( ph -> A e. ( ZZ>= ` 2 ) )
  assume jm3.1.b: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume jm3.1.c: |- ( ph -> N e. NN )
  assume jm3.1.d: |- ( ph -> ( K rmY ( N + 1 ) ) <_ A )


  assert |- ( ph -> ( K ^ N ) < ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) - 1 ) )

  proof
    wph
    cK
    cN
    cexp
    co
    #
    cA
    c2
    cA
    cmul
    co
    #
    cK
    cmul
    co
    #
    cK
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
    wph
    cK
    cN
    wph
    cK
    c2
    cuz
    cfv
    #
    wcel
    #
    cK
    cr
    wcel
    #
    jm3.1.b
    c2
    cK
    eluzelre
    syl
    #
    wph
    cN
    jm3.1.c
    nnnn0d
    reexpcld
    #
    wph
    cA
    @6
    wcel
    #
    cA
    cr
    wcel
    #
    jm3.1.a
    c2
    cA
    eluzelre
    syl
    #
    wph
    @4
    cr
    wcel
    c1
    cr
    wcel
    #
    @5
    cr
    wcel
    wph
    @2
    @3
    wph
    @1
    cK
    wph
    c2
    cr
    wcel
    @12
    @1
    cr
    wcel
    2re
    @13
    c2
    cA
    remulcl
    sylancr
    @9
    remulcld
    wph
    cK
    @9
    resqcld
    #
    resubcld
    1re
    @4
    c1
    resubcl
    sylancl
    #
    wph
    cA
    cK
    cN
    jm3.1.a
    jm3.1.b
    jm3.1.c
    jm3.1.d
    jm3.1lem1
    #
    wph
    cA
    cA
    cK
    cmul
    co
    #
    cK
    c1
    cmin
    co
    #
    caddc
    co
    #
    @5
    @13
    wph
    @18
    @19
    wph
    cA
    cK
    @13
    @9
    remulcld
    #
    wph
    @8
    @14
    @19
    cr
    wcel
    @9
    1re
    cK
    c1
    resubcl
    sylancl
    readdcld
    #
    @16
    wph
    cA
    @18
    @20
    @13
    @21
    @22
    wph
    c1
    cK
    clt
    wbr
    #
    cA
    @18
    clt
    wbr
    #
    wph
    @7
    @23
    jm3.1.b
    @7
    cK
    cz
    wcel
    #
    @23
    cK
    eluz2b1
    simprbi
    syl
    wph
    @12
    @8
    cc0
    cA
    clt
    wbr
    @23
    @24
    wb
    @13
    @9
    wph
    cA
    wph
    @11
    cA
    cn
    wcel
    jm3.1.a
    cA
    eluz2nn
    syl
    nngt0d
    cA
    cK
    ltmulgt11
    syl3anc
    mpbid
    wph
    @18
    @19
    @21
    wph
    @19
    wph
    @7
    @19
    cn
    wcel
    jm3.1.b
    cK
    uz2m1nn
    syl
    nnrpd
    ltaddrpd
    lttrd
    wph
    cK
    c1
    caddc
    co
    #
    cK
    cmul
    co
    #
    @18
    c1
    cmin
    co
    #
    @3
    cmin
    co
    #
    caddc
    co
    #
    @18
    @29
    caddc
    co
    #
    @20
    @5
    cle
    wph
    @27
    @18
    @29
    wph
    @26
    cK
    wph
    @8
    @26
    cr
    wcel
    #
    @9
    cK
    peano2re
    syl
    #
    @9
    remulcld
    #
    @21
    wph
    @28
    @3
    wph
    @18
    cr
    wcel
    @14
    @28
    cr
    wcel
    @21
    1re
    @18
    c1
    resubcl
    sylancl
    #
    @15
    resubcld
    wph
    @26
    cA
    cle
    wbr
    #
    @27
    @18
    cle
    wbr
    #
    wph
    cK
    cA
    clt
    wbr
    #
    @36
    wph
    cK
    @0
    cA
    @9
    @10
    @13
    wph
    cK
    c1
    cexp
    co
    cK
    @0
    cle
    wph
    cK
    wph
    cK
    @9
    recnd
    #
    exp1d
    wph
    cK
    c1
    cN
    @9
    wph
    cK
    wph
    @7
    cK
    cn
    wcel
    jm3.1.b
    cK
    eluz2nn
    syl
    #
    nnge1d
    wph
    cN
    cn
    c1
    cuz
    cfv
    jm3.1.c
    nnuz
    syl6eleq
    leexp2ad
    eqbrtrrd
    @17
    lelttrd
    wph
    @25
    cA
    cz
    wcel
    #
    @38
    @36
    wb
    wph
    @7
    @25
    jm3.1.b
    c2
    cK
    eluzelz
    syl
    wph
    @11
    @41
    jm3.1.a
    c2
    cA
    eluzelz
    syl
    cK
    cA
    zltp1le
    syl2anc
    mpbid
    wph
    @32
    @12
    @8
    cc0
    cK
    clt
    wbr
    @36
    @37
    wb
    @33
    @13
    @9
    wph
    cK
    @40
    nngt0d
    @26
    cA
    cK
    lemul1
    syl112anc
    mpbid
    leadd1dd
    wph
    @18
    @27
    @3
    cmin
    co
    #
    c1
    cmin
    co
    #
    caddc
    co
    @42
    @28
    caddc
    co
    @20
    @30
    wph
    @18
    @42
    c1
    wph
    @18
    @21
    recnd
    #
    wph
    @42
    wph
    @27
    @3
    @34
    @15
    resubcld
    recnd
    wph
    1cnd
    #
    addsub12d
    wph
    @43
    @19
    @18
    caddc
    wph
    @42
    cK
    c1
    cmin
    wph
    @42
    cK
    cK
    cmul
    co
    #
    c1
    cK
    cmul
    co
    #
    caddc
    co
    #
    @46
    cmin
    co
    @47
    cK
    wph
    @27
    @48
    @3
    @46
    cmin
    wph
    cK
    c1
    cK
    @39
    @45
    @39
    adddird
    wph
    cK
    @39
    sqvald
    oveq12d
    wph
    @46
    @47
    wph
    cK
    cK
    @39
    @39
    mulcld
    wph
    c1
    cc
    wcel
    cK
    cc
    wcel
    @47
    cc
    wcel
    ax-1cn
    @39
    c1
    cK
    mulcl
    sylancr
    pncan2d
    wph
    cK
    @39
    mulid2d
    3eqtrd
    oveq1d
    oveq2d
    wph
    @27
    @3
    @28
    wph
    @27
    @34
    recnd
    wph
    @3
    @15
    recnd
    #
    wph
    @28
    @35
    recnd
    #
    subadd23d
    3eqtr3d
    wph
    @5
    @18
    @18
    caddc
    co
    #
    @3
    cmin
    co
    #
    c1
    cmin
    co
    @51
    c1
    cmin
    co
    #
    @3
    cmin
    co
    #
    @31
    wph
    @4
    @52
    c1
    cmin
    wph
    @2
    @51
    @3
    cmin
    wph
    @2
    c2
    @18
    cmul
    co
    @51
    wph
    c2
    cA
    cK
    wph
    2cnd
    wph
    cA
    @13
    recnd
    @39
    mulassd
    wph
    @18
    @44
    2timesd
    eqtrd
    oveq1d
    oveq1d
    wph
    @51
    @3
    c1
    wph
    @51
    wph
    @18
    @18
    @21
    @21
    readdcld
    recnd
    @49
    @45
    sub32d
    wph
    @54
    @18
    @28
    caddc
    co
    #
    @3
    cmin
    co
    @31
    wph
    @53
    @55
    @3
    cmin
    wph
    @18
    @18
    c1
    @44
    @44
    @45
    addsubassd
    oveq1d
    wph
    @18
    @28
    @3
    @44
    @50
    @49
    addsubassd
    eqtrd
    3eqtrd
    3brtr4d
    ltletrd
    lttrd
end
