include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cz.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "cmul.mm"
include "caddc.mm"
include "cpell14qr.mm"
include "cpellfund.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crmx.mm"
include "crmy.mm"
include "wa.mm"
include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wb.mm"
include "rmspecnonsq.mm"
include "3ad2ant1.mm"
include "pellfund14b.mm"
include "syl.mm"
include "cr.mm"
include "nn0re.mm"
include "3ad2ant2.mm"
include "rmspecpos.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "zre.mm"
include "3ad2ant3.mm"
include "remulcld.mm"
include "readdcld.mm"
include "biantrurd.mm"
include "simpl2.mm"
include "simpl3.mm"
include "eqidd.mm"
include "simpr.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "ex.mm"
include "cc.mm"
include "cq.mm"
include "rmspecsqrtnq.mm"
include "adantr.mm"
include "nn0ssq.mm"
include "simp2.mm"
include "sseldi.mm"
include "zq.mm"
include "sseli.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "qirropth.mm"
include "syl122anc.mm"
include "biimpd.mm"
include "anim1d.mm"
include "oveqan12d.mm"
include "eqcomd.mm"
include "biimpa.mm"
include "syl6.mm"
include "rexlimdvva.mm"
include "impbid.mm"
include "elpell14qr.mm"
include "3bitr4d.mm"
include "cxp.mm"
include "wf.mm"
include "frmx.mm"
include "a1i.mm"
include "simpl1.mm"
include "fovrnd.mm"
include "zssq.mm"
include "frmy.mm"
include "rmxyval.mm"
include "3ad2antl1.mm"
include "rmspecfund.mm"
include "eqtr4d.mm"
include "bitr3d.mm"
include "rexbidva.mm"

theorem rmxycomplete
  let cA: class A
  let vn: setvar n
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y

  disjoint A n
  disjoint X n
  disjoint Y n
  disjoint X x
  disjoint X y
  disjoint x y
  disjoint Y x
  disjoint Y y
  disjoint A x
  disjoint A y
  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ X e. NN0 /\ Y e. ZZ ) -> ( ( ( X ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( Y ^ 2 ) ) ) = 1 <-> E. n e. ZZ ( X = ( A rmX n ) /\ Y = ( A rmY n ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cX
    cn0
    wcel
    #
    cY
    cz
    wcel
    #
    w3a
    #
    cX
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    cY
    cmul
    co
    #
    caddc
    co
    #
    @5
    cpell14qr
    cfv
    wcel
    #
    @8
    @5
    cpellfund
    cfv
    #
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    cX
    c2
    cexp
    co
    #
    @5
    cY
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
    cX
    cA
    @11
    crmx
    co
    #
    wceq
    cY
    cA
    @11
    crmy
    co
    #
    wceq
    wa
    #
    vn
    cz
    wrex
    @4
    @5
    cn
    csquarenn
    cdif
    wcel
    #
    @9
    @14
    wb
    @1
    @2
    @23
    @3
    cA
    rmspecnonsq
    3ad2ant1
    #
    vn
    @8
    @5
    pellfund14b
    syl
    @4
    @8
    vx
    cv
    #
    @6
    vy
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
    @25
    c2
    cexp
    co
    #
    @5
    @26
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
    vy
    cz
    wrex
    vx
    cn0
    wrex
    #
    @8
    cr
    wcel
    #
    @36
    wa
    #
    @19
    @9
    @4
    @37
    @36
    @4
    cX
    @7
    @2
    @1
    cX
    cr
    wcel
    @3
    cX
    nn0re
    3ad2ant2
    @4
    @6
    cY
    @1
    @2
    @6
    cr
    wcel
    @3
    @1
    @6
    @1
    @5
    cA
    rmspecpos
    rpsqrtcld
    rpred
    3ad2ant1
    @3
    @1
    cY
    cr
    wcel
    @2
    cY
    zre
    3ad2ant3
    remulcld
    readdcld
    biantrurd
    @4
    @19
    @36
    @4
    @19
    @36
    @4
    @19
    wa
    #
    @2
    @3
    @8
    @8
    wceq
    #
    @19
    @36
    @1
    @2
    @3
    @19
    simpl2
    @1
    @2
    @3
    @19
    simpl3
    @39
    @8
    eqidd
    @4
    @19
    simpr
    @35
    @40
    @19
    wa
    @8
    cX
    @27
    caddc
    co
    #
    wceq
    #
    @15
    @32
    cmin
    co
    #
    c1
    wceq
    #
    wa
    vx
    vy
    cX
    cY
    cn0
    cz
    @25
    cX
    wceq
    #
    @29
    @42
    @34
    @44
    @45
    @28
    @41
    @8
    @25
    cX
    @27
    caddc
    oveq1
    eqeq2d
    @45
    @33
    @43
    c1
    @45
    @30
    @15
    @32
    cmin
    @25
    cX
    c2
    cexp
    oveq1
    oveq1d
    eqeq1d
    anbi12d
    @26
    cY
    wceq
    #
    @42
    @40
    @44
    @19
    @46
    @41
    @8
    @8
    @46
    @27
    @7
    cX
    caddc
    @26
    cY
    @6
    cmul
    oveq2
    oveq2d
    eqeq2d
    @46
    @43
    @18
    c1
    @46
    @32
    @17
    @15
    cmin
    @46
    @31
    @16
    @5
    cmul
    @26
    cY
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    ex
    @4
    @35
    @19
    vx
    vy
    cn0
    cz
    @4
    @25
    cn0
    wcel
    #
    @26
    cz
    wcel
    #
    wa
    #
    wa
    #
    @35
    cX
    @25
    wceq
    #
    cY
    @26
    wceq
    #
    wa
    #
    @34
    wa
    @19
    @50
    @29
    @53
    @34
    @50
    @29
    @53
    @50
    @6
    cc
    cq
    cdif
    wcel
    #
    cX
    cq
    wcel
    #
    cY
    cq
    wcel
    #
    @25
    cq
    wcel
    #
    @26
    cq
    wcel
    #
    @29
    @53
    wb
    @4
    @54
    @49
    @1
    @2
    @54
    @3
    cA
    rmspecsqrtnq
    3ad2ant1
    #
    adantr
    @4
    @55
    @49
    @4
    cn0
    cq
    cX
    nn0ssq
    @1
    @2
    @3
    simp2
    sseldi
    #
    adantr
    @4
    @56
    @49
    @3
    @1
    @56
    @2
    cY
    zq
    3ad2ant3
    #
    adantr
    @47
    @57
    @4
    @48
    cn0
    cq
    @25
    nn0ssq
    sseli
    ad2antrl
    @48
    @58
    @4
    @47
    @26
    zq
    ad2antll
    @6
    cX
    cY
    @25
    @26
    qirropth
    syl122anc
    biimpd
    anim1d
    @53
    @34
    @19
    @53
    @33
    @18
    c1
    @53
    @18
    @33
    @51
    @52
    @15
    @30
    @17
    @32
    cmin
    cX
    @25
    c2
    cexp
    oveq1
    @52
    @16
    @31
    @5
    cmul
    cY
    @26
    c2
    cexp
    oveq1
    oveq2d
    oveqan12d
    eqcomd
    eqeq1d
    biimpa
    syl6
    rexlimdvva
    impbid
    @4
    @23
    @9
    @38
    wb
    @24
    vx
    vy
    @8
    @5
    elpell14qr
    syl
    3bitr4d
    @4
    @22
    @13
    vn
    cz
    @4
    @11
    cz
    wcel
    #
    wa
    #
    @8
    @20
    @6
    @21
    cmul
    co
    caddc
    co
    #
    wceq
    #
    @22
    @13
    @63
    @54
    @55
    @56
    @20
    cq
    wcel
    @21
    cq
    wcel
    @65
    @22
    wb
    @4
    @54
    @62
    @59
    adantr
    @4
    @55
    @62
    @60
    adantr
    @4
    @56
    @62
    @61
    adantr
    @63
    cn0
    cq
    @20
    nn0ssq
    @63
    cA
    @11
    cn0
    @0
    cz
    crmx
    @0
    cz
    cxp
    #
    cn0
    crmx
    wf
    @63
    frmx
    a1i
    @1
    @2
    @3
    @62
    simpl1
    #
    @4
    @62
    simpr
    #
    fovrnd
    sseldi
    @63
    cz
    cq
    @21
    zssq
    @63
    cA
    @11
    cz
    @0
    cz
    crmy
    @66
    cz
    crmy
    wf
    @63
    frmy
    a1i
    @67
    @68
    fovrnd
    sseldi
    @6
    cX
    cY
    @20
    @21
    qirropth
    syl122anc
    @63
    @64
    @12
    @8
    @63
    @64
    cA
    @6
    caddc
    co
    #
    @11
    cexp
    co
    #
    @12
    @1
    @2
    @62
    @64
    @70
    wceq
    @3
    cA
    @11
    rmxyval
    3ad2antl1
    @63
    @10
    @69
    @11
    cexp
    @4
    @10
    @69
    wceq
    #
    @62
    @1
    @2
    @71
    @3
    cA
    rmspecfund
    3ad2ant1
    adantr
    oveq1d
    eqtr4d
    eqeq2d
    bitr3d
    rexbidva
    3bitr4d
end
