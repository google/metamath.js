include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1234qr.mm"
include "cfv.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "cv.mm"
include "csqrt.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cz.mm"
include "wrex.mm"
include "elpell1234qr.mm"
include "biimpa.mm"
include "pell1234qrre.mm"
include "pell1234qrne0.mm"
include "rereccld.mm"
include "ad2antrr.mm"
include "cneg.mm"
include "simplrl.mm"
include "simplrr.mm"
include "znegcld.mm"
include "cc.mm"
include "recnd.mm"
include "zcn.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "eldifi.mm"
include "nncnd.mm"
include "ad3antrrr.mm"
include "sqrtcld.mm"
include "zcnd.mm"
include "negcld.mm"
include "mulcld.mm"
include "addcld.mm"
include "cc0.mm"
include "wne.mm"
include "sqmuld.mm"
include "sqsqrtd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "simprr.mm"
include "subsq.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "recidd.mm"
include "simprl.mm"
include "mulneg2d.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "mulcanad.mm"
include "sqneg.mm"
include "syl.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "jca.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "adantld.mm"
include "mpd.mm"
include "wb.mm"
include "mpbird.mm"

theorem pell1234qrreccl
  let cA: class A
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) -> ( 1 / A ) e. ( Pell1234QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell1234qr
    cfv
    #
    wcel
    #
    wa
    #
    c1
    cA
    cdiv
    co
    #
    @1
    wcel
    #
    @4
    cr
    wcel
    #
    @4
    vc
    cv
    #
    cD
    csqrt
    cfv
    #
    vd
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @7
    c2
    cexp
    co
    #
    cD
    @9
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    vd
    cz
    wrex
    vc
    cz
    wrex
    #
    wa
    #
    @3
    cA
    cr
    wcel
    #
    cA
    va
    cv
    #
    @8
    vb
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @22
    c2
    cexp
    co
    #
    cD
    @23
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    wa
    #
    @20
    @0
    @2
    @34
    va
    vb
    cA
    cD
    elpell1234qr
    biimpa
    @3
    @33
    @20
    @21
    @3
    @32
    @20
    va
    vb
    cz
    cz
    @3
    @22
    cz
    wcel
    #
    @23
    cz
    wcel
    #
    wa
    #
    wa
    #
    @32
    @20
    @38
    @32
    wa
    #
    @6
    @19
    @3
    @6
    @37
    @32
    @3
    cA
    cA
    cD
    pell1234qrre
    #
    cA
    cD
    pell1234qrne0
    #
    rereccld
    #
    ad2antrr
    @39
    @35
    @23
    cneg
    #
    cz
    wcel
    @4
    @22
    @8
    @43
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @27
    cD
    @43
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    @19
    @3
    @35
    @36
    @32
    simplrl
    @39
    @23
    @3
    @35
    @36
    @32
    simplrr
    #
    znegcld
    @39
    @4
    @45
    cA
    @3
    @4
    cc
    wcel
    @37
    @32
    @3
    @4
    @42
    recnd
    ad2antrr
    @39
    @22
    @44
    @37
    @22
    cc
    wcel
    #
    @3
    @32
    @35
    @52
    @36
    @22
    zcn
    adantr
    ad2antlr
    #
    @39
    @8
    @43
    @39
    cD
    @0
    cD
    cc
    wcel
    @2
    @37
    @32
    @0
    cD
    cD
    cn
    csquarenn
    eldifi
    nncnd
    ad3antrrr
    #
    sqrtcld
    #
    @39
    @23
    @39
    @23
    @51
    zcnd
    #
    negcld
    mulcld
    addcld
    @3
    cA
    cc
    wcel
    @37
    @32
    @3
    cA
    @40
    recnd
    ad2antrr
    #
    @3
    cA
    cc0
    wne
    @37
    @32
    @41
    ad2antrr
    #
    @39
    c1
    @25
    @22
    @24
    cmin
    co
    #
    cmul
    co
    #
    cA
    @4
    cmul
    co
    cA
    @45
    cmul
    co
    @39
    @30
    @27
    @24
    c2
    cexp
    co
    #
    cmin
    co
    #
    c1
    @60
    @39
    @29
    @61
    @27
    cmin
    @39
    @61
    @8
    c2
    cexp
    co
    #
    @28
    cmul
    co
    @29
    @39
    @8
    @23
    @55
    @56
    sqmuld
    @39
    @63
    cD
    @28
    cmul
    @39
    cD
    @54
    sqsqrtd
    oveq1d
    eqtr2d
    oveq2d
    @38
    @26
    @31
    simprr
    #
    @39
    @52
    @24
    cc
    wcel
    @62
    @60
    wceq
    @53
    @39
    @8
    @23
    @55
    @56
    mulcld
    #
    @22
    @24
    subsq
    syl2anc
    3eqtr3d
    @39
    cA
    @57
    @58
    recidd
    @39
    cA
    @25
    @45
    @59
    cmul
    @38
    @26
    @31
    simprl
    @39
    @45
    @22
    @24
    cneg
    #
    caddc
    co
    @59
    @39
    @44
    @66
    @22
    caddc
    @39
    @8
    @23
    @55
    @56
    mulneg2d
    oveq2d
    @39
    @22
    @24
    @53
    @65
    negsubd
    eqtrd
    oveq12d
    3eqtr4d
    mulcanad
    @39
    @49
    @30
    c1
    @39
    @48
    @29
    @27
    cmin
    @39
    @47
    @28
    cD
    cmul
    @39
    @23
    cc
    wcel
    @47
    @28
    wceq
    @56
    @23
    sqneg
    syl
    oveq2d
    oveq2d
    @64
    eqtrd
    @18
    @46
    @50
    wa
    @4
    @22
    @10
    caddc
    co
    #
    wceq
    #
    @27
    @15
    cmin
    co
    #
    c1
    wceq
    #
    wa
    vc
    vd
    @22
    @43
    cz
    cz
    vc
    va
    weq
    #
    @12
    @68
    @17
    @70
    @71
    @11
    @67
    @4
    @7
    @22
    @10
    caddc
    oveq1
    eqeq2d
    @71
    @16
    @69
    c1
    @71
    @13
    @27
    @15
    cmin
    @7
    @22
    c2
    cexp
    oveq1
    oveq1d
    eqeq1d
    anbi12d
    @9
    @43
    wceq
    #
    @68
    @46
    @70
    @50
    @72
    @67
    @45
    @4
    @72
    @10
    @44
    @22
    caddc
    @9
    @43
    @8
    cmul
    oveq2
    oveq2d
    eqeq2d
    @72
    @69
    @49
    c1
    @72
    @15
    @48
    @27
    cmin
    @72
    @14
    @47
    cD
    cmul
    @9
    @43
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    jca
    ex
    rexlimdvva
    adantld
    mpd
    @0
    @5
    @20
    wb
    @2
    vc
    vd
    @4
    cD
    elpell1234qr
    adantr
    mpbird
end
