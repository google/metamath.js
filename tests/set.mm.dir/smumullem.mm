include "cn0.mm"
include "wcel.mm"
include "cbits.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cin.mm"
include "csmu.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "in0.mm"
include "oveq1d.mm"
include "wss.mm"
include "bitsss.mm"
include "smu02.mm"
include "ax-mp.mm"
include "cc.mm"
include "2cn.mm"
include "exp0.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "zmod10.mm"
include "syl.mm"
include "zcnd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "0bits.mm"
include "syl6req.mm"
include "wa.mm"
include "cmin.mm"
include "crab.mm"
include "csad.mm"
include "oveq1.mm"
include "a1i.mm"
include "simpr.mm"
include "smup1.mm"
include "cif.mm"
include "bitsinv1lem.mm"
include "sylan.mm"
include "adantr.mm"
include "cn.mm"
include "2nn.mm"
include "nnexpcld.mm"
include "zmodcld.mm"
include "nn0cnd.mm"
include "nnnn0d.mm"
include "0nn0.mm"
include "ifcl.mm"
include "sylancl.mm"
include "adddird.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "nn0zd.mm"
include "zmulcld.mm"
include "sadadd.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "bitsshft.mm"
include "ibar.mm"
include "rabbidv.mm"
include "sylan9req.mm"
include "wn.mm"
include "mul01d.mm"
include "wral.mm"
include "intnanrd.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "3eqtr4a.mm"
include "ifbothda.mm"
include "3eqtr2d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem smumullem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  assume smumullem.a: |- ( ph -> A e. ZZ )
  assume smumullem.b: |- ( ph -> B e. ZZ )
  assume smumullem.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( ( ( bits ` A ) i^i ( 0 ..^ N ) ) smul ( bits ` B ) ) = ( bits ` ( ( A mod ( 2 ^ N ) ) x. B ) ) )

  proof
    cN
    cn0
    wcel
    wph
    cA
    cbits
    cfv
    #
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    cB
    cbits
    cfv
    #
    csmu
    co
    #
    cA
    c2
    cN
    cexp
    co
    #
    cmo
    co
    #
    cB
    cmul
    co
    #
    cbits
    cfv
    #
    wceq
    #
    smumullem.n
    wph
    @0
    cc0
    vx
    cv
    #
    cfzo
    co
    #
    cin
    #
    @3
    csmu
    co
    #
    cA
    c2
    @10
    cexp
    co
    #
    cmo
    co
    #
    cB
    cmul
    co
    #
    cbits
    cfv
    #
    wceq
    #
    wi
    wph
    c0
    cA
    c1
    cmo
    co
    #
    cB
    cmul
    co
    #
    cbits
    cfv
    #
    wceq
    #
    wi
    wph
    @0
    cc0
    vk
    cv
    #
    cfzo
    co
    #
    cin
    #
    @3
    csmu
    co
    #
    cA
    c2
    @23
    cexp
    co
    #
    cmo
    co
    #
    cB
    cmul
    co
    #
    cbits
    cfv
    #
    wceq
    #
    wi
    wph
    @0
    cc0
    @23
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cin
    #
    @3
    csmu
    co
    #
    cA
    c2
    @32
    cexp
    co
    #
    cmo
    co
    #
    cB
    cmul
    co
    #
    cbits
    cfv
    #
    wceq
    #
    wi
    wph
    @9
    wi
    vx
    vk
    cN
    @10
    cc0
    wceq
    #
    @18
    @22
    wph
    @41
    @13
    c0
    @17
    @21
    @41
    @13
    c0
    @3
    csmu
    co
    #
    c0
    @41
    @12
    c0
    @3
    csmu
    @41
    @12
    @0
    c0
    cin
    c0
    @41
    @11
    c0
    @0
    @41
    @11
    cc0
    cc0
    cfzo
    co
    c0
    @10
    cc0
    cc0
    cfzo
    oveq2
    cc0
    fzo0
    syl6eq
    ineq2d
    @0
    in0
    syl6eq
    oveq1d
    @3
    cn0
    wss
    #
    @42
    c0
    wceq
    cB
    bitsss
    #
    @3
    smu02
    ax-mp
    syl6eq
    @41
    @16
    @20
    cbits
    @41
    @15
    @19
    cB
    cmul
    @41
    @14
    c1
    cA
    cmo
    @41
    @14
    c2
    cc0
    cexp
    co
    #
    c1
    @10
    cc0
    c2
    cexp
    oveq2
    c2
    cc
    wcel
    @45
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    syl6eq
    oveq2d
    oveq1d
    fveq2d
    eqeq12d
    imbi2d
    @10
    @23
    wceq
    #
    @18
    @31
    wph
    @46
    @13
    @26
    @17
    @30
    @46
    @12
    @25
    @3
    csmu
    @46
    @11
    @24
    @0
    @10
    @23
    cc0
    cfzo
    oveq2
    ineq2d
    oveq1d
    @46
    @16
    @29
    cbits
    @46
    @15
    @28
    cB
    cmul
    @46
    @14
    @27
    cA
    cmo
    @10
    @23
    c2
    cexp
    oveq2
    oveq2d
    oveq1d
    fveq2d
    eqeq12d
    imbi2d
    @10
    @32
    wceq
    #
    @18
    @40
    wph
    @47
    @13
    @35
    @17
    @39
    @47
    @12
    @34
    @3
    csmu
    @47
    @11
    @33
    @0
    @10
    @32
    cc0
    cfzo
    oveq2
    ineq2d
    oveq1d
    @47
    @16
    @38
    cbits
    @47
    @15
    @37
    cB
    cmul
    @47
    @14
    @36
    cA
    cmo
    @10
    @32
    c2
    cexp
    oveq2
    oveq2d
    oveq1d
    fveq2d
    eqeq12d
    imbi2d
    @10
    cN
    wceq
    #
    @18
    @9
    wph
    @48
    @13
    @4
    @17
    @8
    @48
    @12
    @2
    @3
    csmu
    @48
    @11
    @1
    @0
    @10
    cN
    cc0
    cfzo
    oveq2
    ineq2d
    oveq1d
    @48
    @16
    @7
    cbits
    @48
    @15
    @6
    cB
    cmul
    @48
    @14
    @5
    cA
    cmo
    @10
    cN
    c2
    cexp
    oveq2
    oveq2d
    oveq1d
    fveq2d
    eqeq12d
    imbi2d
    wph
    @21
    cc0
    cbits
    cfv
    #
    c0
    wph
    @20
    cc0
    cbits
    wph
    @20
    cc0
    cB
    cmul
    co
    cc0
    wph
    @19
    cc0
    cB
    cmul
    wph
    cA
    cz
    wcel
    #
    @19
    cc0
    wceq
    smumullem.a
    cA
    zmod10
    syl
    oveq1d
    wph
    cB
    wph
    cB
    smumullem.b
    zcnd
    #
    mul02d
    eqtrd
    fveq2d
    0bits
    syl6req
    @23
    cn0
    wcel
    #
    wph
    @31
    @40
    wph
    @52
    @31
    @40
    wi
    @31
    @40
    wph
    @52
    wa
    #
    @26
    @23
    @0
    wcel
    #
    vn
    cv
    @23
    cmin
    co
    @3
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    @30
    @57
    csad
    co
    #
    wceq
    @26
    @30
    @57
    csad
    oveq1
    @53
    @35
    @58
    @39
    @59
    @53
    @0
    @3
    vn
    @23
    @0
    cn0
    wss
    @53
    cA
    bitsss
    a1i
    @43
    @53
    @44
    a1i
    wph
    @52
    simpr
    #
    smup1
    @53
    @39
    @29
    cB
    @54
    @27
    cc0
    cif
    #
    cmul
    co
    #
    caddc
    co
    #
    cbits
    cfv
    #
    @30
    @62
    cbits
    cfv
    #
    csad
    co
    #
    @59
    @53
    @38
    @63
    cbits
    @53
    @38
    @28
    @61
    caddc
    co
    #
    cB
    cmul
    co
    @29
    @61
    cB
    cmul
    co
    #
    caddc
    co
    @63
    @53
    @37
    @67
    cB
    cmul
    wph
    @50
    @52
    @37
    @67
    wceq
    smumullem.a
    @23
    cA
    bitsinv1lem
    sylan
    oveq1d
    @53
    @28
    @61
    cB
    @53
    @28
    @53
    cA
    @27
    wph
    @50
    @52
    smumullem.a
    adantr
    @53
    c2
    @23
    c2
    cn
    wcel
    @53
    2nn
    a1i
    @60
    nnexpcld
    #
    zmodcld
    #
    nn0cnd
    @53
    @61
    @53
    @27
    cn0
    wcel
    cc0
    cn0
    wcel
    @61
    cn0
    wcel
    @53
    @27
    @69
    nnnn0d
    0nn0
    @54
    @27
    cc0
    cn0
    ifcl
    sylancl
    #
    nn0cnd
    #
    wph
    cB
    cc
    wcel
    #
    @52
    @51
    adantr
    #
    adddird
    @53
    @68
    @62
    @29
    caddc
    @53
    @61
    cB
    @72
    @74
    mulcomd
    oveq2d
    3eqtrd
    fveq2d
    @53
    @29
    cz
    wcel
    @62
    cz
    wcel
    @66
    @64
    wceq
    @53
    @28
    cB
    @53
    @28
    @70
    nn0zd
    wph
    cB
    cz
    wcel
    #
    @52
    smumullem.b
    adantr
    #
    zmulcld
    @53
    cB
    @61
    @76
    @53
    @61
    @71
    nn0zd
    zmulcld
    @29
    @62
    sadadd
    syl2anc
    @53
    @65
    @57
    @30
    csad
    @54
    cB
    @27
    cmul
    co
    #
    cbits
    cfv
    #
    @57
    wceq
    cB
    cc0
    cmul
    co
    #
    cbits
    cfv
    #
    @57
    wceq
    @65
    @57
    wceq
    @53
    @27
    cc0
    @27
    @61
    wceq
    #
    @78
    @65
    @57
    @81
    @77
    @62
    cbits
    @27
    @61
    cB
    cmul
    oveq2
    fveq2d
    eqeq1d
    cc0
    @61
    wceq
    #
    @80
    @65
    @57
    @82
    @79
    @62
    cbits
    cc0
    @61
    cB
    cmul
    oveq2
    fveq2d
    eqeq1d
    @53
    @54
    @78
    @55
    vn
    cn0
    crab
    #
    @57
    wph
    @75
    @52
    @83
    @78
    wceq
    smumullem.b
    cB
    vn
    @23
    bitsshft
    sylan
    @54
    @55
    @56
    vn
    cn0
    @54
    @55
    ibar
    rabbidv
    sylan9req
    @53
    @54
    wn
    #
    wa
    #
    @49
    c0
    @80
    @57
    0bits
    @85
    @79
    cc0
    cbits
    @85
    cB
    @53
    @73
    @84
    @74
    adantr
    mul01d
    fveq2d
    @85
    @56
    wn
    #
    vn
    cn0
    wral
    @57
    c0
    wceq
    @85
    @86
    vn
    cn0
    @85
    @54
    @55
    @53
    @84
    simpr
    intnanrd
    ralrimivw
    @56
    vn
    cn0
    rabeq0
    sylibr
    3eqtr4a
    ifbothda
    oveq2d
    3eqtr2d
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    mpcom
end
