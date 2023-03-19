include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1234qr.mm"
include "cfv.mm"
include "cpell14qr.mm"
include "cneg.mm"
include "wo.mm"
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
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "elpell1234qr.mm"
include "cn0.mm"
include "wi.mm"
include "simp-4r.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rspcev.mm"
include "adantll.mm"
include "wb.mm"
include "elpell14qr.mm"
include "ad4antr.mm"
include "mpbir2and.mm"
include "orcd.mm"
include "exp31.mm"
include "simp-5r.mm"
include "renegcld.mm"
include "simpllr.mm"
include "znegcl.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "negeqd.mm"
include "cc.mm"
include "zcn.mm"
include "ad4antlr.mm"
include "eldifi.mm"
include "nncnd.mm"
include "ad5antr.mm"
include "sqrtcld.mm"
include "mulcld.mm"
include "negdid.mm"
include "mulneg2.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "sqneg.mm"
include "syl.mm"
include "oveq12d.mm"
include "simprr.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "olcd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "elznn0.mm"
include "simprbi.mm"
include "adantl.mm"
include "mpjaod.mm"
include "expimpd.mm"
include "sylbid.mm"
include "imp.mm"

theorem pell1234qrdich
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


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell1234QR ` D ) ) -> ( A e. ( Pell14QR ` D ) \/ -u A e. ( Pell14QR ` D ) ) )

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
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    cA
    cneg
    #
    @2
    wcel
    #
    wo
    #
    @0
    @1
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
    @8
    c2
    cexp
    co
    #
    cD
    @10
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
    #
    va
    cz
    wrex
    #
    wa
    @6
    va
    vb
    cA
    cD
    elpell1234qr
    @0
    @7
    @21
    @6
    @0
    @7
    wa
    #
    @20
    @6
    va
    cz
    @22
    @8
    cz
    wcel
    #
    wa
    #
    @8
    cn0
    wcel
    #
    @20
    @6
    wi
    #
    @8
    cneg
    #
    cn0
    wcel
    #
    @24
    @25
    @20
    @6
    @24
    @25
    wa
    @20
    wa
    #
    @3
    @5
    @29
    @3
    @7
    cA
    vc
    cv
    #
    @11
    caddc
    co
    #
    wceq
    #
    @30
    c2
    cexp
    co
    #
    @16
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
    #
    vc
    cn0
    wrex
    #
    @0
    @7
    @23
    @25
    @20
    simp-4r
    @25
    @20
    @38
    @24
    @37
    @20
    vc
    @8
    cn0
    vc
    va
    weq
    #
    @36
    @19
    vb
    cz
    @39
    @32
    @13
    @35
    @18
    @39
    @31
    @12
    cA
    @30
    @8
    @11
    caddc
    oveq1
    eqeq2d
    @39
    @34
    @17
    c1
    @39
    @33
    @14
    @16
    cmin
    @30
    @8
    c2
    cexp
    oveq1
    oveq1d
    eqeq1d
    anbi12d
    rexbidv
    rspcev
    adantll
    @0
    @3
    @7
    @38
    wa
    wb
    @7
    @23
    @25
    @20
    vc
    vb
    cA
    cD
    elpell14qr
    ad4antr
    mpbir2and
    orcd
    exp31
    @24
    @28
    @26
    @24
    @28
    wa
    #
    @19
    @6
    vb
    cz
    @40
    @10
    cz
    wcel
    #
    wa
    #
    @19
    @6
    @42
    @19
    wa
    #
    @5
    @3
    @43
    @5
    @4
    cr
    wcel
    #
    @4
    @30
    @9
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
    @33
    cD
    @45
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
    cn0
    wrex
    #
    @43
    cA
    @0
    @7
    @23
    @28
    @41
    @19
    simp-5r
    renegcld
    @43
    @28
    @10
    cneg
    #
    cz
    wcel
    #
    @4
    @27
    @9
    @55
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @27
    c2
    cexp
    co
    #
    cD
    @55
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
    @54
    @24
    @28
    @41
    @19
    simpllr
    @41
    @56
    @40
    @19
    @10
    znegcl
    ad2antlr
    @43
    @4
    @12
    cneg
    @27
    @11
    cneg
    #
    caddc
    co
    @58
    @43
    cA
    @12
    @42
    @13
    @18
    simprl
    negeqd
    @43
    @8
    @11
    @23
    @8
    cc
    wcel
    #
    @22
    @28
    @41
    @19
    @8
    zcn
    ad4antlr
    #
    @43
    @9
    @10
    @43
    cD
    @0
    cD
    cc
    wcel
    @7
    @23
    @28
    @41
    @19
    @0
    cD
    cD
    cn
    csquarenn
    eldifi
    nncnd
    ad5antr
    sqrtcld
    #
    @41
    @10
    cc
    wcel
    #
    @40
    @19
    @10
    zcn
    ad2antlr
    #
    mulcld
    negdid
    @43
    @65
    @57
    @27
    caddc
    @43
    @9
    cc
    wcel
    #
    @69
    @65
    @57
    wceq
    @68
    @70
    @71
    @69
    wa
    @57
    @65
    @9
    @10
    mulneg2
    eqcomd
    syl2anc
    oveq2d
    3eqtrd
    @43
    @63
    @17
    c1
    @43
    @60
    @14
    @62
    @16
    cmin
    @43
    @66
    @60
    @14
    wceq
    @67
    @8
    sqneg
    syl
    @43
    @61
    @15
    cD
    cmul
    @43
    @69
    @61
    @15
    wceq
    @70
    @10
    sqneg
    syl
    oveq2d
    oveq12d
    @42
    @13
    @18
    simprr
    eqtrd
    @53
    @59
    @64
    wa
    @4
    @27
    @46
    caddc
    co
    #
    wceq
    #
    @60
    @50
    cmin
    co
    #
    c1
    wceq
    #
    wa
    vc
    vd
    @27
    @55
    cn0
    cz
    @30
    @27
    wceq
    #
    @48
    @73
    @52
    @75
    @76
    @47
    @72
    @4
    @30
    @27
    @46
    caddc
    oveq1
    eqeq2d
    @76
    @51
    @74
    c1
    @76
    @33
    @60
    @50
    cmin
    @30
    @27
    c2
    cexp
    oveq1
    oveq1d
    eqeq1d
    anbi12d
    @45
    @55
    wceq
    #
    @73
    @59
    @75
    @64
    @77
    @72
    @58
    @4
    @77
    @46
    @57
    @27
    caddc
    @45
    @55
    @9
    cmul
    oveq2
    oveq2d
    eqeq2d
    @77
    @74
    @63
    c1
    @77
    @50
    @62
    @60
    cmin
    @77
    @49
    @61
    cD
    cmul
    @45
    @55
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    @0
    @5
    @44
    @54
    wa
    wb
    @7
    @23
    @28
    @41
    @19
    vc
    vd
    @4
    cD
    elpell14qr
    ad5antr
    mpbir2and
    olcd
    ex
    rexlimdva
    ex
    @23
    @25
    @28
    wo
    #
    @22
    @23
    @8
    cr
    wcel
    @78
    @8
    elznn0
    simprbi
    adantl
    mpjaod
    rexlimdva
    expimpd
    sylbid
    imp
end
