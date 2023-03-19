include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "c4.mm"
include "cmin.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "sqcld.mm"
include "eqeltrd.mm"
include "addcld.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "sqdivd.mm"
include "sq2.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "4cn.mm"
include "4ne0.mm"
include "divcld.mm"
include "subcld.mm"
include "subdird.mm"
include "div23d.mm"
include "eqcomd.mm"
include "divcan1d.mm"
include "oveq12d.mm"
include "wceq.mm"
include "c3.mm"
include "binom2.mm"
include "syl2anc.mm"
include "mulcld.mm"
include "adddird.mm"
include "c1.mm"
include "df-3.mm"
include "cn0.mm"
include "2nn0.mm"
include "expp1.mm"
include "sylancl.mm"
include "syl5req.mm"
include "mulassd.mm"
include "mul32d.mm"
include "eqtr3d.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "3nn0.mm"
include "expcl.mm"
include "addsubassd.mm"
include "eqtr4d.mm"
include "cneg.mm"
include "negcld.mm"
include "addassd.mm"
include "negsubd.mm"
include "3eqtr3d.mm"
include "subeq0d.mm"
include "wb.mm"
include "subsub23.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "divsubdird.mm"
include "divcan3d.mm"
include "mulcan2ad.mm"

theorem dquartlem2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cI: class I
  let cM: class M
  let cX: class X
  assume dquart.b: |- ( ph -> B e. CC )
  assume dquart.c: |- ( ph -> C e. CC )
  assume dquart.x: |- ( ph -> X e. CC )
  assume dquart.s: |- ( ph -> S e. CC )
  assume dquart.m: |- ( ph -> M = ( ( 2 x. S ) ^ 2 ) )
  assume dquart.m0: |- ( ph -> M =/= 0 )
  assume dquart.i: |- ( ph -> I e. CC )
  assume dquart.i2: |- ( ph -> ( I ^ 2 ) = ( ( -u ( S ^ 2 ) - ( B / 2 ) ) + ( ( C / 4 ) / S ) ) )
  assume dquart.d: |- ( ph -> D e. CC )
  assume dquart.3: |- ( ph -> ( ( ( M ^ 3 ) + ( ( 2 x. B ) x. ( M ^ 2 ) ) ) + ( ( ( ( B ^ 2 ) - ( 4 x. D ) ) x. M ) + -u ( C ^ 2 ) ) ) = 0 )


  assert |- ( ph -> ( ( ( ( M + B ) / 2 ) ^ 2 ) - ( ( ( C ^ 2 ) / 4 ) / M ) ) = D )

  proof
    wph
    cM
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    c2
    cexp
    co
    #
    cC
    c2
    cexp
    co
    #
    c4
    cdiv
    co
    #
    cM
    cdiv
    co
    #
    cmin
    co
    @0
    c2
    cexp
    co
    #
    c4
    cdiv
    co
    #
    @4
    cmin
    co
    #
    cD
    wph
    @1
    @6
    @4
    cmin
    wph
    @1
    @5
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    @6
    wph
    @0
    c2
    wph
    cM
    cB
    wph
    cM
    c2
    cS
    cmul
    co
    #
    c2
    cexp
    co
    cc
    dquart.m
    wph
    @9
    wph
    c2
    cc
    wcel
    #
    cS
    cc
    wcel
    @9
    cc
    wcel
    2cn
    dquart.s
    c2
    cS
    mulcl
    sylancr
    sqcld
    eqeltrd
    #
    dquart.b
    addcld
    #
    @10
    wph
    2cn
    a1i
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    sqdivd
    @8
    c4
    @5
    cdiv
    sq2
    oveq2i
    syl6eq
    oveq1d
    wph
    @7
    cD
    cM
    wph
    @6
    @4
    wph
    @5
    c4
    wph
    @0
    @12
    sqcld
    #
    c4
    cc
    wcel
    #
    wph
    4cn
    a1i
    #
    c4
    cc0
    wne
    wph
    4ne0
    a1i
    #
    divcld
    #
    wph
    @3
    cM
    wph
    @2
    c4
    wph
    cC
    dquart.c
    sqcld
    #
    @16
    @17
    divcld
    #
    @11
    dquart.m0
    divcld
    #
    subcld
    dquart.d
    @11
    dquart.m0
    wph
    @7
    cM
    cmul
    co
    @6
    cM
    cmul
    co
    #
    @4
    cM
    cmul
    co
    #
    cmin
    co
    @5
    cM
    cmul
    co
    #
    c4
    cdiv
    co
    #
    @3
    cmin
    co
    #
    cD
    cM
    cmul
    co
    #
    wph
    @6
    @4
    cM
    @18
    @21
    @11
    subdird
    wph
    @22
    @25
    @23
    @3
    cmin
    wph
    @25
    @22
    wph
    @5
    cM
    c4
    @14
    @11
    @16
    @17
    div23d
    eqcomd
    wph
    @3
    cM
    @20
    @11
    dquart.m0
    divcan1d
    oveq12d
    wph
    @24
    @2
    cmin
    co
    #
    c4
    cdiv
    co
    c4
    @27
    cmul
    co
    #
    c4
    cdiv
    co
    @26
    @27
    wph
    @28
    @29
    c4
    cdiv
    wph
    @28
    c4
    cD
    cmul
    co
    #
    cM
    cmul
    co
    #
    @29
    wph
    @24
    @31
    cmin
    co
    #
    @2
    wceq
    #
    @28
    @31
    wceq
    #
    wph
    @32
    cM
    c3
    cexp
    co
    #
    c2
    cB
    cmul
    co
    #
    cM
    c2
    cexp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cB
    c2
    cexp
    co
    #
    cM
    cmul
    co
    #
    caddc
    co
    #
    @31
    cmin
    co
    #
    @39
    @40
    @30
    cmin
    co
    #
    cM
    cmul
    co
    #
    caddc
    co
    #
    @2
    wph
    @24
    @42
    @31
    cmin
    wph
    @24
    @37
    c2
    cM
    cB
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @40
    caddc
    co
    #
    cM
    cmul
    co
    @49
    cM
    cmul
    co
    #
    @41
    caddc
    co
    @42
    wph
    @5
    @50
    cM
    cmul
    wph
    cM
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @5
    @50
    wceq
    @11
    dquart.b
    cM
    cB
    binom2
    syl2anc
    oveq1d
    wph
    @49
    @40
    cM
    wph
    @37
    @48
    wph
    cM
    @11
    sqcld
    #
    wph
    @10
    @47
    cc
    wcel
    @48
    cc
    wcel
    2cn
    wph
    cM
    cB
    @11
    dquart.b
    mulcld
    c2
    @47
    mulcl
    sylancr
    #
    addcld
    wph
    cB
    dquart.b
    sqcld
    #
    @11
    adddird
    wph
    @51
    @39
    @41
    caddc
    wph
    @51
    @37
    cM
    cmul
    co
    #
    @48
    cM
    cmul
    co
    #
    caddc
    co
    @39
    wph
    @37
    @48
    cM
    @54
    @55
    @11
    adddird
    wph
    @57
    @35
    @58
    @38
    caddc
    wph
    @35
    cM
    c2
    c1
    caddc
    co
    #
    cexp
    co
    #
    @57
    c3
    @59
    cM
    cexp
    df-3
    oveq2i
    wph
    @52
    c2
    cn0
    wcel
    @60
    @57
    wceq
    @11
    2nn0
    cM
    c2
    expp1
    sylancl
    syl5req
    wph
    @36
    cM
    cmul
    co
    #
    cM
    cmul
    co
    @36
    cM
    cM
    cmul
    co
    #
    cmul
    co
    @58
    @38
    wph
    @36
    cM
    cM
    wph
    @10
    @53
    @36
    cc
    wcel
    2cn
    dquart.b
    c2
    cB
    mulcl
    sylancr
    #
    @11
    @11
    mulassd
    wph
    @48
    @61
    cM
    cmul
    wph
    c2
    cM
    cmul
    co
    cB
    cmul
    co
    @48
    @61
    wph
    c2
    cM
    cB
    @13
    @11
    dquart.b
    mulassd
    wph
    c2
    cM
    cB
    @13
    @11
    dquart.b
    mul32d
    eqtr3d
    oveq1d
    wph
    @37
    @62
    @36
    cmul
    wph
    cM
    @11
    sqvald
    oveq2d
    3eqtr4d
    oveq12d
    eqtrd
    oveq1d
    3eqtrd
    oveq1d
    wph
    @43
    @39
    @41
    @31
    cmin
    co
    #
    caddc
    co
    @46
    wph
    @39
    @41
    @31
    wph
    @35
    @38
    wph
    @52
    c3
    cn0
    wcel
    @35
    cc
    wcel
    @11
    3nn0
    cM
    c3
    expcl
    sylancl
    wph
    @36
    @37
    @63
    @54
    mulcld
    addcld
    #
    wph
    @40
    cM
    @56
    @11
    mulcld
    wph
    @30
    cM
    wph
    @15
    cD
    cc
    wcel
    @30
    cc
    wcel
    4cn
    dquart.d
    c4
    cD
    mulcl
    sylancr
    #
    @11
    mulcld
    #
    addsubassd
    wph
    @45
    @64
    @39
    caddc
    wph
    @40
    @30
    cM
    @56
    @66
    @11
    subdird
    oveq2d
    eqtr4d
    wph
    @46
    @2
    wph
    @39
    @45
    @65
    wph
    @44
    cM
    wph
    @40
    @30
    @56
    @66
    subcld
    @11
    mulcld
    #
    addcld
    #
    @19
    wph
    @46
    @2
    cneg
    #
    caddc
    co
    @39
    @45
    @70
    caddc
    co
    caddc
    co
    @46
    @2
    cmin
    co
    cc0
    wph
    @39
    @45
    @70
    @65
    @68
    wph
    @2
    @19
    negcld
    addassd
    wph
    @46
    @2
    @69
    @19
    negsubd
    dquart.3
    3eqtr3d
    subeq0d
    3eqtrd
    wph
    @24
    cc
    wcel
    @31
    cc
    wcel
    @2
    cc
    wcel
    @33
    @34
    wb
    wph
    @5
    cM
    @14
    @11
    mulcld
    #
    @67
    @19
    @24
    @31
    @2
    subsub23
    syl3anc
    mpbid
    wph
    c4
    cD
    cM
    @16
    dquart.d
    @11
    mulassd
    eqtrd
    oveq1d
    wph
    @24
    @2
    c4
    @71
    @19
    @16
    @17
    divsubdird
    wph
    @27
    c4
    wph
    cD
    cM
    dquart.d
    @11
    mulcld
    @16
    @17
    divcan3d
    3eqtr3d
    3eqtrd
    mulcan2ad
    eqtrd
end
