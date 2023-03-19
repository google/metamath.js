include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "wa.mm"
include "cr.mm"
include "cv.mm"
include "csqrt.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "c1.mm"
include "cz.mm"
include "wrex.mm"
include "cn0.mm"
include "cpell1qr.mm"
include "cdiv.mm"
include "wo.mm"
include "elpell14qr.mm"
include "biimpa.mm"
include "cneg.mm"
include "simplrr.mm"
include "elznn0.mm"
include "sylib.mm"
include "simprd.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simpr.mm"
include "rsp2e.mm"
include "syl3anc.mm"
include "jca.mm"
include "ex.mm"
include "wb.mm"
include "elpell1qr.mm"
include "ad4antr.mm"
include "sylibrd.mm"
include "cc0.mm"
include "wne.mm"
include "pell14qrne0.mm"
include "rereccld.mm"
include "cc.mm"
include "pell14qrre.mm"
include "recnd.mm"
include "reccld.mm"
include "ad3antrrr.mm"
include "nn0cn.mm"
include "ad2antrl.mm"
include "eldifi.mm"
include "nncnd.mm"
include "sqrtcld.mm"
include "zcn.mm"
include "ad2antll.mm"
include "negcld.mm"
include "mulcld.mm"
include "addcld.mm"
include "adantr.mm"
include "recidd.mm"
include "simprr.mm"
include "eqtr4d.mm"
include "subsq.mm"
include "syl2anc.mm"
include "sqmuld.mm"
include "sqsqrtd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "mulneg2d.mm"
include "negsub.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "adantrr.mm"
include "eqtrd.mm"
include "mulcanad.mm"
include "sqneg.mm"
include "syl.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "rspe.mm"
include "orim12d.mm"
include "mpd.mm"
include "rexlimdvva.mm"
include "expimpd.mm"

theorem pell14qrdich
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) ) -> ( A e. ( Pell1QR ` D ) \/ ( 1 / A ) e. ( Pell1QR ` D ) ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    wcel
    #
    wa
    #
    cA
    cr
    wcel
    #
    cA
    va
    cv
    #
    cD
    csqrt
    cfv
    #
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
    @4
    c2
    cexp
    co
    #
    cD
    @6
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
    cn0
    wrex
    #
    wa
    #
    cA
    cD
    cpell1qr
    cfv
    #
    wcel
    #
    c1
    cA
    cdiv
    co
    #
    @18
    wcel
    #
    wo
    #
    @0
    @1
    @17
    va
    vb
    cA
    cD
    elpell14qr
    biimpa
    @2
    @3
    @16
    @22
    @2
    @3
    wa
    #
    @15
    @22
    va
    vb
    cn0
    cz
    @23
    @4
    cn0
    wcel
    #
    @6
    cz
    wcel
    #
    wa
    #
    wa
    #
    @15
    @22
    @27
    @15
    wa
    #
    @6
    cn0
    wcel
    #
    @6
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    @22
    @28
    @6
    cr
    wcel
    #
    @32
    @28
    @25
    @33
    @32
    wa
    @23
    @24
    @25
    @15
    simplrr
    @6
    elznn0
    sylib
    simprd
    @28
    @29
    @19
    @31
    @21
    @28
    @29
    @3
    @15
    vb
    cn0
    wrex
    va
    cn0
    wrex
    #
    wa
    #
    @19
    @28
    @29
    @35
    @28
    @29
    wa
    #
    @3
    @34
    @27
    @3
    @15
    @29
    @2
    @3
    @26
    simplr
    #
    ad2antrr
    @36
    @24
    @29
    @15
    @34
    @27
    @24
    @15
    @29
    @23
    @24
    @25
    simprl
    #
    ad2antrr
    @28
    @29
    simpr
    @27
    @15
    @29
    simplr
    @15
    va
    vb
    cn0
    cn0
    rsp2e
    syl3anc
    jca
    ex
    @0
    @19
    @35
    wb
    @1
    @3
    @26
    @15
    va
    vb
    cA
    cD
    elpell1qr
    ad4antr
    sylibrd
    @28
    @31
    @20
    cr
    wcel
    #
    @20
    @4
    @5
    vc
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
    @10
    cD
    @40
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
    vc
    cn0
    wrex
    #
    va
    cn0
    wrex
    #
    wa
    #
    @21
    @28
    @31
    @51
    @28
    @31
    wa
    #
    @39
    @50
    @52
    cA
    @27
    @3
    @15
    @31
    @37
    ad2antrr
    @2
    cA
    cc0
    wne
    #
    @3
    @26
    @15
    @31
    cA
    cD
    pell14qrne0
    #
    ad4antr
    rereccld
    @52
    @24
    @49
    @50
    @27
    @24
    @15
    @31
    @38
    ad2antrr
    @52
    @31
    @20
    @4
    @5
    @30
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @10
    cD
    @30
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
    @49
    @28
    @31
    simpr
    @52
    @57
    @61
    @28
    @57
    @31
    @28
    @20
    @56
    cA
    @2
    @20
    cc
    wcel
    @3
    @26
    @15
    @2
    cA
    @2
    cA
    cA
    cD
    pell14qrre
    recnd
    #
    @54
    reccld
    ad3antrrr
    @27
    @56
    cc
    wcel
    @15
    @27
    @4
    @55
    @24
    @4
    cc
    wcel
    #
    @23
    @25
    @4
    nn0cn
    ad2antrl
    #
    @27
    @5
    @30
    @27
    cD
    @0
    cD
    cc
    wcel
    @1
    @3
    @26
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
    @27
    @6
    @25
    @6
    cc
    wcel
    #
    @23
    @24
    @6
    zcn
    ad2antll
    #
    negcld
    mulcld
    addcld
    adantr
    @2
    cA
    cc
    wcel
    @3
    @26
    @15
    @63
    ad3antrrr
    @2
    @53
    @3
    @26
    @15
    @54
    ad3antrrr
    @28
    cA
    @20
    cmul
    co
    #
    @13
    cA
    @56
    cmul
    co
    #
    @28
    @70
    c1
    @13
    @2
    @70
    c1
    wceq
    @3
    @26
    @15
    @2
    cA
    @63
    @54
    recidd
    ad3antrrr
    @27
    @9
    @14
    simprr
    eqtr4d
    @27
    @9
    @13
    @71
    wceq
    @14
    @27
    @9
    wa
    #
    @10
    @7
    c2
    cexp
    co
    #
    cmin
    co
    #
    @8
    @4
    @7
    cmin
    co
    #
    cmul
    co
    #
    @13
    @71
    @72
    @64
    @7
    cc
    wcel
    #
    @74
    @76
    wceq
    @27
    @64
    @9
    @65
    adantr
    @27
    @77
    @9
    @27
    @5
    @6
    @67
    @69
    mulcld
    #
    adantr
    @4
    @7
    subsq
    syl2anc
    @27
    @13
    @74
    wceq
    @9
    @27
    @12
    @73
    @10
    cmin
    @27
    @73
    @5
    c2
    cexp
    co
    #
    @11
    cmul
    co
    @12
    @27
    @5
    @6
    @67
    @69
    sqmuld
    @27
    @79
    cD
    @11
    cmul
    @27
    cD
    @66
    sqsqrtd
    oveq1d
    eqtr2d
    oveq2d
    adantr
    @72
    cA
    @8
    @56
    @75
    cmul
    @27
    @9
    simpr
    @27
    @56
    @75
    wceq
    @9
    @27
    @56
    @4
    @7
    cneg
    #
    caddc
    co
    #
    @75
    @27
    @55
    @80
    @4
    caddc
    @27
    @5
    @6
    @67
    @69
    mulneg2d
    oveq2d
    @27
    @64
    @77
    @75
    @81
    wceq
    @65
    @78
    @64
    @77
    wa
    @81
    @75
    @4
    @7
    negsub
    eqcomd
    syl2anc
    eqtr4d
    adantr
    oveq12d
    3eqtr4d
    adantrr
    eqtrd
    mulcanad
    adantr
    @52
    @60
    @13
    c1
    @52
    @59
    @12
    @10
    cmin
    @52
    @58
    @11
    cD
    cmul
    @52
    @68
    @58
    @11
    wceq
    @27
    @68
    @15
    @31
    @69
    ad2antrr
    @6
    sqneg
    syl
    oveq2d
    oveq2d
    @27
    @9
    @14
    @31
    simplrr
    eqtrd
    jca
    @48
    @62
    vc
    @30
    cn0
    @40
    @30
    wceq
    #
    @43
    @57
    @47
    @61
    @82
    @42
    @56
    @20
    @82
    @41
    @55
    @4
    caddc
    @40
    @30
    @5
    cmul
    oveq2
    oveq2d
    eqeq2d
    @82
    @46
    @60
    c1
    @82
    @45
    @59
    @10
    cmin
    @82
    @44
    @58
    cD
    cmul
    @40
    @30
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq1d
    anbi12d
    rspcev
    syl2anc
    @49
    va
    cn0
    rspe
    syl2anc
    jca
    ex
    @0
    @21
    @51
    wb
    @1
    @3
    @26
    @15
    va
    vc
    @20
    cD
    elpell1qr
    ad4antr
    sylibrd
    orim12d
    mpd
    ex
    rexlimdvva
    expimpd
    mpd
end
