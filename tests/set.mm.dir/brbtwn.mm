include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "cc0.mm"
include "cicc.mm"
include "wrex.mm"
include "wa.mm"
include "cn.mm"
include "coprab.mm"
include "ccnv.mm"
include "df-btwn.mm"
include "breqi.mm"
include "wb.mm"
include "cvv.mm"
include "opex.mm"
include "brcnvg.mm"
include "mpan2.mm"
include "3ad2ant1.mm"
include "df-br.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "rexralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "3anbi2d.mm"
include "3anbi3d.mm"
include "eqeq1d.mm"
include "eloprabg.mm"
include "simp1.mm"
include "eedimeq.mm"
include "syl2anr.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "syl.mm"
include "biimpd.mm"
include "expimpd.mm"
include "rexlimdvw.mm"
include "wi.mm"
include "eleenn.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "exp32.mm"
include "mpcom.mm"
include "impbid.mm"
include "bitrd.mm"
include "3comr.mm"
include "syl5bb.mm"

theorem brbtwn
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let vi: setvar i
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n

  disjoint N i
  disjoint N t
  disjoint i t
  disjoint A i
  disjoint A t
  disjoint B i
  disjoint B t
  disjoint C i
  disjoint C t
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N n
  disjoint x y
  disjoint x z
  disjoint i x
  disjoint t x
  disjoint n x
  disjoint y z
  disjoint i y
  disjoint t y
  disjoint n y
  disjoint i z
  disjoint t z
  disjoint n z
  disjoint i n
  disjoint n t
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B n
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C n
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) -> ( A Btwn <. B , C >. <-> E. t e. ( 0 [,] 1 ) A. i e. ( 1 ... N ) ( A ` i ) = ( ( ( 1 - t ) x. ( B ` i ) ) + ( t x. ( C ` i ) ) ) ) )

  proof
    cA
    cB
    cC
    cop
    #
    cbtwn
    wbr
    cA
    @0
    vy
    cv
    #
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    vz
    cv
    #
    @3
    wcel
    #
    vx
    cv
    #
    @3
    wcel
    #
    w3a
    #
    vi
    cv
    #
    @7
    cfv
    #
    c1
    vt
    cv
    #
    cmin
    co
    #
    @10
    @1
    cfv
    #
    cmul
    co
    #
    @12
    @10
    @5
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    @2
    cfz
    co
    #
    wral
    vt
    cc0
    c1
    cicc
    co
    #
    wrex
    #
    wa
    #
    vn
    cn
    wrex
    #
    vy
    vz
    vx
    coprab
    #
    ccnv
    #
    wbr
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @28
    wcel
    #
    cC
    @28
    wcel
    #
    w3a
    #
    @10
    cA
    cfv
    #
    @13
    @10
    cB
    cfv
    #
    cmul
    co
    #
    @12
    @10
    cC
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    vt
    @21
    wrex
    #
    cA
    @0
    cbtwn
    @26
    vy
    vx
    vz
    vt
    vi
    vn
    df-btwn
    breqi
    @32
    @27
    @0
    cA
    @25
    wbr
    #
    @42
    @29
    @30
    @27
    @43
    wb
    #
    @31
    @29
    @0
    cvv
    wcel
    @44
    cB
    cC
    opex
    cA
    @0
    @28
    cvv
    @25
    brcnvg
    mpan2
    3ad2ant1
    @43
    @0
    cA
    cop
    @25
    wcel
    #
    @32
    @42
    @0
    cA
    @25
    df-br
    @30
    @31
    @29
    @45
    @42
    wb
    @30
    @31
    @29
    w3a
    #
    @45
    cB
    @3
    wcel
    #
    cC
    @3
    wcel
    #
    cA
    @3
    wcel
    #
    w3a
    #
    @39
    vi
    @20
    wral
    #
    vt
    @21
    wrex
    #
    wa
    #
    vn
    cn
    wrex
    #
    @42
    @24
    @47
    @6
    @8
    w3a
    #
    @11
    @35
    @17
    caddc
    co
    #
    wceq
    #
    vi
    @20
    wral
    vt
    @21
    wrex
    #
    wa
    #
    vn
    cn
    wrex
    @47
    @48
    @8
    w3a
    #
    @11
    @38
    wceq
    #
    vi
    @20
    wral
    vt
    @21
    wrex
    #
    wa
    #
    vn
    cn
    wrex
    @54
    vy
    vz
    vx
    cB
    cC
    cA
    @28
    @28
    @28
    @1
    cB
    wceq
    #
    @23
    @59
    vn
    cn
    @64
    @9
    @55
    @22
    @58
    @64
    @4
    @47
    @6
    @8
    @1
    cB
    @3
    eleq1
    3anbi1d
    @64
    @19
    @57
    vt
    vi
    @21
    @20
    @64
    @18
    @56
    @11
    @64
    @15
    @35
    @17
    caddc
    @64
    @14
    @34
    @13
    cmul
    @10
    @1
    cB
    fveq1
    oveq2d
    oveq1d
    eqeq2d
    rexralbidv
    anbi12d
    rexbidv
    @5
    cC
    wceq
    #
    @59
    @63
    vn
    cn
    @65
    @55
    @60
    @58
    @62
    @65
    @6
    @48
    @47
    @8
    @5
    cC
    @3
    eleq1
    3anbi2d
    @65
    @57
    @61
    vt
    vi
    @21
    @20
    @65
    @56
    @38
    @11
    @65
    @17
    @37
    @35
    caddc
    @65
    @16
    @36
    @12
    cmul
    @10
    @5
    cC
    fveq1
    oveq2d
    oveq2d
    eqeq2d
    rexralbidv
    anbi12d
    rexbidv
    @7
    cA
    wceq
    #
    @63
    @53
    vn
    cn
    @66
    @60
    @50
    @62
    @52
    @66
    @8
    @49
    @47
    @48
    @7
    cA
    @3
    eleq1
    3anbi3d
    @66
    @61
    @39
    vt
    vi
    @21
    @20
    @66
    @11
    @33
    @38
    @10
    @7
    cA
    fveq1
    eqeq1d
    rexralbidv
    anbi12d
    rexbidv
    eloprabg
    @46
    @54
    @42
    @46
    @53
    @42
    vn
    cn
    @46
    @50
    @52
    @42
    @46
    @50
    wa
    #
    @52
    @42
    @67
    @2
    cN
    wceq
    #
    @52
    @42
    wb
    @50
    @47
    @30
    @68
    @46
    @47
    @48
    @49
    simp1
    @30
    @31
    @29
    simp1
    cB
    cN
    @2
    eedimeq
    syl2anr
    @68
    @51
    @41
    vt
    @21
    @68
    @39
    vi
    @20
    @40
    @2
    cN
    c1
    cfz
    oveq2
    raleqdv
    rexbidv
    #
    syl
    biimpd
    expimpd
    rexlimdvw
    cN
    cn
    wcel
    #
    @46
    @42
    @54
    wi
    @30
    @31
    @70
    @29
    cB
    cN
    eleenn
    3ad2ant1
    @70
    @46
    @42
    @54
    @53
    @46
    @42
    wa
    vn
    cN
    cn
    @68
    @50
    @46
    @52
    @42
    @68
    @47
    @30
    @48
    @31
    @49
    @29
    @68
    @3
    @28
    cB
    @2
    cN
    cee
    fveq2
    #
    eleq2d
    @68
    @3
    @28
    cC
    @71
    eleq2d
    @68
    @3
    @28
    cA
    @71
    eleq2d
    3anbi123d
    @69
    anbi12d
    rspcev
    exp32
    mpcom
    impbid
    bitrd
    3comr
    syl5bb
    bitrd
    syl5bb
end
