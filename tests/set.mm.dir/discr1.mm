include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "c1.mm"
include "cif.mm"
include "cneg.mm"
include "cdiv.mm"
include "adantr.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "readdcld.mm"
include "peano2re.mm"
include "syl.mm"
include "renegcld.mm"
include "lt0neg1d.mm"
include "biimpa.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "1re.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wn.mm"
include "resqcl.mm"
include "remulcld.mm"
include "a1i.mm"
include "max2.mm"
include "sylancr.mm"
include "max1.mm"
include "syl6breqr.mm"
include "lemulge11d.mm"
include "letrd.mm"
include "leadd2dd.mm"
include "recnd.mm"
include "adddird.mm"
include "addassd.mm"
include "mulassd.mm"
include "cc.mm"
include "sqval.mm"
include "eqtr4d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "breqtrrd.mm"
include "cmin.mm"
include "ltp1d.mm"
include "wb.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "mulneg1d.mm"
include "df-neg.mm"
include "syl6eq.mm"
include "breqtrd.mm"
include "ltaddsub2d.mm"
include "mpbird.mm"
include "0lt1.mm"
include "ltmul1.mm"
include "mul02d.mm"
include "lelttrd.mm"
include "ltnle.mm"
include "pm2.65da.mm"
include "wo.mm"
include "lelttric.mm"
include "ord.mm"
include "mt3d.mm"

theorem discr1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  assume discr.1: |- ( ph -> A e. RR )
  assume discr.2: |- ( ph -> B e. RR )
  assume discr.3: |- ( ph -> C e. RR )
  assume discr.4: |- ( ( ph /\ x e. RR ) -> 0 <_ ( ( ( A x. ( x ^ 2 ) ) + ( B x. x ) ) + C ) )
  assume discr1.5: |- X = if ( 1 <_ ( ( ( B + if ( 0 <_ C , C , 0 ) ) + 1 ) / -u A ) , ( ( ( B + if ( 0 <_ C , C , 0 ) ) + 1 ) / -u A ) , 1 )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint X x
  disjoint ph x
  assert |- ( ph -> 0 <_ A )

  proof
    wph
    cc0
    cA
    cle
    wbr
    #
    cA
    cc0
    clt
    wbr
    #
    wph
    @1
    cc0
    cA
    cX
    c2
    cexp
    co
    #
    cmul
    co
    #
    cB
    cX
    cmul
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    #
    cle
    wbr
    #
    wph
    @1
    wa
    #
    cX
    cr
    wcel
    #
    cc0
    cA
    vx
    cv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    cB
    @10
    cmul
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    #
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @7
    @8
    cX
    c1
    cB
    cc0
    cC
    cle
    wbr
    #
    cC
    cc0
    cif
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    cA
    cneg
    #
    cdiv
    co
    #
    cle
    wbr
    #
    @23
    c1
    cif
    #
    cr
    discr1.5
    @8
    @23
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @25
    cr
    wcel
    @8
    @21
    @22
    @8
    @20
    cr
    wcel
    @21
    cr
    wcel
    #
    @8
    cB
    @19
    wph
    cB
    cr
    wcel
    @1
    discr.2
    adantr
    #
    @8
    cC
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @19
    cr
    wcel
    wph
    @30
    @1
    discr.3
    adantr
    #
    0re
    @18
    cC
    cc0
    cr
    ifcl
    sylancl
    #
    readdcld
    #
    @20
    peano2re
    syl
    #
    @8
    cA
    wph
    cA
    cr
    wcel
    #
    @1
    discr.1
    adantr
    #
    renegcld
    #
    @8
    @22
    wph
    @1
    cc0
    @22
    clt
    wbr
    #
    wph
    cA
    discr.1
    lt0neg1d
    biimpa
    #
    gt0ne0d
    redivcld
    #
    1re
    @24
    @23
    c1
    cr
    ifcl
    sylancl
    syl5eqel
    #
    wph
    @17
    @1
    wph
    @16
    vx
    cr
    discr.4
    ralrimiva
    adantr
    @16
    @7
    vx
    cX
    cr
    @10
    cX
    wceq
    #
    @15
    @6
    cc0
    cle
    @43
    @14
    @5
    cC
    caddc
    @43
    @12
    @3
    @13
    @4
    caddc
    @43
    @11
    @2
    cA
    cmul
    @10
    cX
    c2
    cexp
    oveq1
    oveq2d
    @10
    cX
    cB
    cmul
    oveq2
    oveq12d
    oveq1d
    breq2d
    rspcv
    sylc
    @8
    @6
    cc0
    clt
    wbr
    #
    @7
    wn
    #
    @8
    @6
    cA
    cX
    cmul
    co
    #
    @20
    caddc
    co
    #
    cX
    cmul
    co
    #
    cc0
    @8
    @5
    cC
    @8
    @3
    @4
    @8
    cA
    @2
    @37
    @8
    @9
    @2
    cr
    wcel
    @42
    cX
    resqcl
    syl
    remulcld
    @8
    cB
    cX
    @29
    @42
    remulcld
    readdcld
    #
    @32
    readdcld
    #
    @8
    @47
    cX
    @8
    @46
    @20
    @8
    cA
    cX
    @37
    @42
    remulcld
    #
    @34
    readdcld
    #
    @42
    remulcld
    @31
    @8
    0re
    a1i
    #
    @8
    @6
    @5
    @19
    cX
    cmul
    co
    #
    caddc
    co
    #
    @48
    cle
    @8
    cC
    @54
    @5
    @32
    @8
    @19
    cX
    @33
    @42
    remulcld
    #
    @49
    @8
    cC
    @19
    @54
    @32
    @33
    @56
    @8
    @31
    @30
    cC
    @19
    cle
    wbr
    0re
    @32
    cc0
    cC
    max2
    sylancr
    @8
    @19
    cX
    @33
    @42
    @8
    @31
    @30
    cc0
    @19
    cle
    wbr
    0re
    @32
    cc0
    cC
    max1
    sylancr
    @8
    c1
    @25
    cX
    cle
    @8
    @27
    @26
    c1
    @25
    cle
    wbr
    1re
    @41
    c1
    @23
    max1
    sylancr
    discr1.5
    syl6breqr
    #
    lemulge11d
    letrd
    leadd2dd
    @8
    @46
    cB
    caddc
    co
    #
    @19
    caddc
    co
    #
    cX
    cmul
    co
    @58
    cX
    cmul
    co
    #
    @54
    caddc
    co
    @48
    @55
    @8
    @58
    @19
    cX
    @8
    @58
    @8
    @46
    cB
    @51
    @29
    readdcld
    recnd
    @8
    @19
    @33
    recnd
    #
    @8
    cX
    @42
    recnd
    #
    adddird
    @8
    @59
    @47
    cX
    cmul
    @8
    @46
    cB
    @19
    @8
    @46
    @51
    recnd
    #
    @8
    cB
    @29
    recnd
    #
    @61
    addassd
    oveq1d
    @8
    @60
    @5
    @54
    caddc
    @8
    @60
    @46
    cX
    cmul
    co
    #
    @4
    caddc
    co
    @5
    @8
    @46
    cB
    cX
    @63
    @64
    @62
    adddird
    @8
    @65
    @3
    @4
    caddc
    @8
    @65
    cA
    cX
    cX
    cmul
    co
    #
    cmul
    co
    @3
    @8
    cA
    cX
    cX
    @8
    cA
    @37
    recnd
    #
    @62
    @62
    mulassd
    @8
    @2
    @66
    cA
    cmul
    @8
    cX
    cc
    wcel
    @2
    @66
    wceq
    @62
    cX
    sqval
    syl
    oveq2d
    eqtr4d
    oveq1d
    eqtrd
    oveq1d
    3eqtr3d
    breqtrrd
    @8
    @48
    cc0
    cX
    cmul
    co
    #
    cc0
    clt
    @8
    @47
    cc0
    clt
    wbr
    #
    @48
    @68
    clt
    wbr
    #
    @8
    @69
    @20
    cc0
    @46
    cmin
    co
    #
    clt
    wbr
    @8
    @20
    @22
    cX
    cmul
    co
    #
    @71
    clt
    @8
    @20
    @21
    @72
    @34
    @35
    @8
    @22
    cX
    @38
    @42
    remulcld
    @8
    @20
    @34
    ltp1d
    @8
    @23
    cX
    cle
    wbr
    #
    @21
    @72
    cle
    wbr
    #
    @8
    @23
    @25
    cX
    cle
    @8
    @27
    @26
    @23
    @25
    cle
    wbr
    1re
    @41
    c1
    @23
    max2
    sylancr
    discr1.5
    syl6breqr
    @8
    @28
    @9
    @22
    cr
    wcel
    @39
    @73
    @74
    wb
    @35
    @42
    @38
    @40
    @21
    cX
    @22
    ledivmul
    syl112anc
    mpbid
    ltletrd
    @8
    @72
    @46
    cneg
    @71
    @8
    cA
    cX
    @67
    @62
    mulneg1d
    @46
    df-neg
    syl6eq
    breqtrd
    @8
    @46
    @20
    cc0
    @51
    @34
    @53
    ltaddsub2d
    mpbird
    @8
    @47
    cr
    wcel
    @31
    @9
    cc0
    cX
    clt
    wbr
    @69
    @70
    wb
    @52
    @53
    @42
    @8
    cc0
    c1
    cX
    @53
    @27
    @8
    1re
    a1i
    @42
    cc0
    c1
    clt
    wbr
    @8
    0lt1
    a1i
    @57
    ltletrd
    @47
    cc0
    cX
    ltmul1
    syl112anc
    mpbid
    @8
    cX
    @62
    mul02d
    breqtrd
    lelttrd
    @8
    @6
    cr
    wcel
    @31
    @44
    @45
    wb
    @50
    0re
    @6
    cc0
    ltnle
    sylancl
    mpbid
    pm2.65da
    wph
    @0
    @1
    wph
    @31
    @36
    @0
    @1
    wo
    0re
    discr.1
    cc0
    cA
    lelttric
    sylancr
    ord
    mt3d
end
