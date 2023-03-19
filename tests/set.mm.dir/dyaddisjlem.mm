include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "co.mm"
include "cicc.mm"
include "cfv.mm"
include "wss.mm"
include "cioo.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3o.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "clt.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "simplll.mm"
include "simplrl.mm"
include "dyadval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "simpllr.mm"
include "simplrr.mm"
include "ineq12d.mm"
include "incom.mm"
include "syl6eq.mm"
include "adantr.mm"
include "cmul.mm"
include "wb.mm"
include "zred.mm"
include "recnd.mm"
include "cn.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "div13d.mm"
include "cmin.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "nn0zd.mm"
include "expsubd.mm"
include "2z.mm"
include "simpr.mm"
include "znn0sub.mm"
include "mpbid.mm"
include "zexpcl.mm"
include "eqeltrrd.mm"
include "zmulcld.mm"
include "eqeltrd.mm"
include "zltp1le.mm"
include "cr.mm"
include "nndivred.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltdivmul2.mm"
include "syl112anc.mm"
include "peano2re.mm"
include "syl.mm"
include "ledivmul2.mm"
include "3bitr4d.mm"
include "cxr.mm"
include "wi.mm"
include "rexrd.mm"
include "ioodisj.mm"
include "ex.mm"
include "syl22anc.mm"
include "sylbid.mm"
include "imp.mm"
include "eqtrd.mm"
include "3mix3d.mm"
include "simprl.mm"
include "peano2zd.mm"
include "biimpa.mm"
include "adantrl.mm"
include "iccss.mm"
include "3sstr4d.mm"
include "3mix2d.mm"
include "anassrs.mm"
include "adantlr.mm"
include "ltlecasei.mm"

theorem dyaddisjlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  disjoint F w
  disjoint F z
  assert |- ( ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. NN0 /\ D e. NN0 ) ) /\ C <_ D ) -> ( ( [,] ` ( A F C ) ) C_ ( [,] ` ( B F D ) ) \/ ( [,] ` ( B F D ) ) C_ ( [,] ` ( A F C ) ) \/ ( ( (,) ` ( A F C ) ) i^i ( (,) ` ( B F D ) ) ) = (/) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cn0
    wcel
    #
    cD
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cC
    cD
    cle
    wbr
    #
    wa
    #
    cA
    cC
    cF
    co
    #
    cicc
    cfv
    #
    cB
    cD
    cF
    co
    #
    cicc
    cfv
    #
    wss
    #
    @12
    @10
    wss
    #
    @9
    cioo
    cfv
    #
    @11
    cioo
    cfv
    #
    cin
    #
    c0
    wceq
    #
    w3o
    #
    cB
    c2
    cD
    cexp
    co
    #
    cdiv
    co
    #
    cA
    c2
    cC
    cexp
    co
    #
    cdiv
    co
    #
    @8
    @21
    @23
    clt
    wbr
    #
    wa
    #
    @18
    @13
    @14
    @25
    @17
    @21
    cB
    c1
    caddc
    co
    #
    @20
    cdiv
    co
    #
    cioo
    co
    #
    @23
    cA
    c1
    caddc
    co
    #
    @22
    cdiv
    co
    #
    cioo
    co
    #
    cin
    #
    c0
    @8
    @17
    @32
    wceq
    @24
    @8
    @17
    @31
    @28
    cin
    #
    @32
    @8
    @15
    @31
    @16
    @28
    @8
    @15
    @23
    @30
    cop
    #
    cioo
    cfv
    @31
    @8
    @9
    @34
    cioo
    @8
    @0
    @3
    @9
    @34
    wceq
    @0
    @1
    @5
    @7
    simplll
    #
    @2
    @3
    @4
    @7
    simplrl
    #
    vx
    vy
    cA
    cC
    cF
    dyadmbl.1
    dyadval
    syl2anc
    #
    fveq2d
    @23
    @30
    cioo
    df-ov
    syl6eqr
    @8
    @16
    @21
    @27
    cop
    #
    cioo
    cfv
    @28
    @8
    @11
    @38
    cioo
    @8
    @1
    @4
    @11
    @38
    wceq
    @0
    @1
    @5
    @7
    simpllr
    #
    @2
    @3
    @4
    @7
    simplrr
    #
    vx
    vy
    cB
    cD
    cF
    dyadmbl.1
    dyadval
    syl2anc
    #
    fveq2d
    @21
    @27
    cioo
    df-ov
    syl6eqr
    ineq12d
    #
    @31
    @28
    incom
    syl6eq
    adantr
    @8
    @24
    @32
    c0
    wceq
    #
    @8
    @24
    @27
    @23
    cle
    wbr
    #
    @43
    @8
    cB
    @23
    @20
    cmul
    co
    #
    clt
    wbr
    #
    @26
    @45
    cle
    wbr
    #
    @24
    @44
    @8
    @1
    @45
    cz
    wcel
    @46
    @47
    wb
    @39
    @8
    @45
    @20
    @22
    cdiv
    co
    #
    cA
    cmul
    co
    cz
    @8
    cA
    @22
    @20
    @8
    cA
    @8
    cA
    @35
    zred
    #
    recnd
    @8
    @22
    @8
    c2
    cn
    wcel
    #
    @3
    @22
    cn
    wcel
    2nn
    @36
    c2
    cC
    nnexpcl
    sylancr
    #
    nncnd
    #
    @8
    @20
    @8
    @50
    @4
    @20
    cn
    wcel
    2nn
    @40
    c2
    cD
    nnexpcl
    sylancr
    #
    nncnd
    #
    @8
    @22
    @51
    nnne0d
    #
    div13d
    @8
    @48
    cA
    @8
    c2
    cD
    cC
    cmin
    co
    #
    cexp
    co
    #
    @48
    cz
    @8
    c2
    cD
    cC
    @8
    2cnd
    c2
    cc0
    wne
    @8
    2ne0
    a1i
    @8
    cC
    @36
    nn0zd
    #
    @8
    cD
    @40
    nn0zd
    #
    expsubd
    @8
    c2
    cz
    wcel
    @56
    cn0
    wcel
    #
    @57
    cz
    wcel
    2z
    @8
    @7
    @60
    @6
    @7
    simpr
    @8
    cC
    cz
    wcel
    cD
    cz
    wcel
    @7
    @60
    wb
    @58
    @59
    cC
    cD
    znn0sub
    syl2anc
    mpbid
    c2
    @56
    zexpcl
    sylancr
    eqeltrrd
    #
    @35
    zmulcld
    eqeltrd
    cB
    @45
    zltp1le
    syl2anc
    @8
    cB
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    @20
    cr
    wcel
    #
    cc0
    @20
    clt
    wbr
    #
    @24
    @46
    wb
    @8
    cB
    @39
    zred
    #
    @8
    cA
    @22
    @49
    @51
    nndivred
    #
    @8
    @20
    @53
    nnred
    #
    @8
    @20
    @53
    nngt0d
    #
    cB
    @23
    @20
    ltdivmul2
    syl112anc
    @8
    @26
    cr
    wcel
    #
    @63
    @64
    @65
    @44
    @47
    wb
    @8
    @62
    @70
    @66
    cB
    peano2re
    syl
    #
    @67
    @68
    @69
    @26
    @23
    @20
    ledivmul2
    syl112anc
    3bitr4d
    @8
    @21
    cxr
    wcel
    #
    @27
    cxr
    wcel
    #
    @23
    cxr
    wcel
    #
    @30
    cxr
    wcel
    #
    @44
    @43
    wi
    @8
    @21
    @8
    cB
    @20
    @66
    @53
    nndivred
    #
    rexrd
    #
    @8
    @27
    @8
    @26
    @20
    @71
    @53
    nndivred
    rexrd
    #
    @8
    @23
    @67
    rexrd
    #
    @8
    @30
    @8
    @29
    @22
    @8
    cA
    cr
    wcel
    @29
    cr
    wcel
    @49
    cA
    peano2re
    syl
    #
    @51
    nndivred
    #
    rexrd
    #
    @72
    @73
    wa
    #
    @74
    @75
    wa
    #
    wa
    @44
    @43
    @21
    @27
    @23
    @30
    ioodisj
    ex
    syl22anc
    sylbid
    imp
    eqtrd
    3mix3d
    @8
    @23
    @21
    cle
    wbr
    #
    wa
    @19
    @21
    @30
    @8
    @85
    @21
    @30
    clt
    wbr
    #
    @19
    @8
    @85
    @86
    wa
    #
    wa
    #
    @14
    @13
    @18
    @88
    @21
    @27
    cicc
    co
    #
    @23
    @30
    cicc
    co
    #
    @12
    @10
    @88
    @63
    @30
    cr
    wcel
    #
    @85
    @27
    @30
    cle
    wbr
    #
    @89
    @90
    wss
    @8
    @63
    @87
    @67
    adantr
    @8
    @91
    @87
    @81
    adantr
    @8
    @85
    @86
    simprl
    @8
    @86
    @92
    @85
    @8
    @86
    @92
    @8
    cB
    @30
    @20
    cmul
    co
    #
    clt
    wbr
    #
    @26
    @93
    cle
    wbr
    #
    @86
    @92
    @8
    @1
    @93
    cz
    wcel
    @94
    @95
    wb
    @39
    @8
    @93
    @48
    @29
    cmul
    co
    cz
    @8
    @29
    @22
    @20
    @8
    @29
    @80
    recnd
    @52
    @54
    @55
    div13d
    @8
    @48
    @29
    @61
    @8
    cA
    @35
    peano2zd
    zmulcld
    eqeltrd
    cB
    @93
    zltp1le
    syl2anc
    @8
    @62
    @91
    @64
    @65
    @86
    @94
    wb
    @66
    @81
    @68
    @69
    cB
    @30
    @20
    ltdivmul2
    syl112anc
    @8
    @70
    @91
    @64
    @65
    @92
    @95
    wb
    @71
    @81
    @68
    @69
    @26
    @30
    @20
    ledivmul2
    syl112anc
    3bitr4d
    biimpa
    adantrl
    @23
    @30
    @21
    @27
    iccss
    syl22anc
    @8
    @12
    @89
    wceq
    @87
    @8
    @12
    @38
    cicc
    cfv
    @89
    @8
    @11
    @38
    cicc
    @41
    fveq2d
    @21
    @27
    cicc
    df-ov
    syl6eqr
    adantr
    @8
    @10
    @90
    wceq
    @87
    @8
    @10
    @34
    cicc
    cfv
    @90
    @8
    @9
    @34
    cicc
    @37
    fveq2d
    @23
    @30
    cicc
    df-ov
    syl6eqr
    adantr
    3sstr4d
    3mix2d
    anassrs
    @8
    @30
    @21
    cle
    wbr
    #
    @19
    @85
    @8
    @96
    wa
    #
    @18
    @13
    @14
    @97
    @17
    @33
    c0
    @8
    @17
    @33
    wceq
    @96
    @42
    adantr
    @8
    @96
    @33
    c0
    wceq
    #
    @8
    @74
    @75
    @72
    @73
    @96
    @98
    wi
    @79
    @82
    @77
    @78
    @84
    @83
    wa
    @96
    @98
    @23
    @30
    @21
    @27
    ioodisj
    ex
    syl22anc
    imp
    eqtrd
    3mix3d
    adantlr
    @8
    @21
    cr
    wcel
    @85
    @76
    adantr
    @8
    @91
    @85
    @81
    adantr
    ltlecasei
    @76
    @67
    ltlecasei
end
