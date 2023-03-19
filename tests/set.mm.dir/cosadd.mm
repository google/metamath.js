include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "ce.mm"
include "cneg.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cmin.mm"
include "wceq.mm"
include "addcl.mm"
include "cosval.mm"
include "syl.mm"
include "coscl.mm"
include "adantr.mm"
include "adantl.mm"
include "mulcld.mm"
include "ax-icn.mm"
include "sincl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "ppncand.mm"
include "adddi.mm"
include "mp3an1.mm"
include "fveq2d.mm"
include "simpl.mm"
include "simpr.mm"
include "efadd.mm"
include "syl2anc.mm"
include "efival.mm"
include "oveqan12d.mm"
include "muladdd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "negicn.mm"
include "efmival.mm"
include "mulsubd.mm"
include "oveq12d.mm"
include "2timesd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "c1.mm"
include "a1i.mm"
include "mul4d.mm"
include "ixi.mm"
include "oveq1i.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "mulm1d.mm"
include "negsubd.mm"

theorem cosadd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( cos ` ( A + B ) ) = ( ( ( cos ` A ) x. ( cos ` B ) ) - ( ( sin ` A ) x. ( sin ` B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    ccos
    cfv
    #
    ci
    @3
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @3
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c2
    cA
    ccos
    cfv
    #
    cB
    ccos
    cfv
    #
    cmul
    co
    #
    ci
    cB
    csin
    cfv
    #
    cmul
    co
    #
    ci
    cA
    csin
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @14
    @17
    @15
    cmul
    co
    #
    cmin
    co
    #
    @2
    @3
    cc
    wcel
    @4
    @11
    wceq
    cA
    cB
    addcl
    @3
    cosval
    syl
    @2
    @10
    @21
    c2
    cdiv
    @2
    @20
    @12
    @16
    cmul
    co
    #
    @13
    @18
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @20
    @27
    cmin
    co
    #
    caddc
    co
    @20
    @20
    caddc
    co
    @10
    @21
    @2
    @20
    @27
    @20
    @2
    @14
    @19
    @2
    @12
    @13
    @0
    @12
    cc
    wcel
    @1
    cA
    coscl
    adantr
    #
    @1
    @13
    cc
    wcel
    @0
    cB
    coscl
    adantl
    #
    mulcld
    #
    @2
    @16
    @18
    @2
    ci
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @16
    cc
    wcel
    ax-icn
    @1
    @34
    @0
    cB
    sincl
    adantl
    #
    ci
    @15
    mulcl
    sylancr
    #
    @2
    @33
    @17
    cc
    wcel
    #
    @18
    cc
    wcel
    ax-icn
    @0
    @37
    @1
    cA
    sincl
    adantr
    #
    ci
    @17
    mulcl
    sylancr
    #
    mulcld
    addcld
    #
    @2
    @25
    @26
    @2
    @12
    @16
    @30
    @36
    mulcld
    @2
    @13
    @18
    @31
    @39
    mulcld
    addcld
    @40
    ppncand
    @2
    @6
    @28
    @9
    @29
    caddc
    @2
    @6
    ci
    cA
    cmul
    co
    #
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    @41
    ce
    cfv
    #
    @42
    ce
    cfv
    #
    cmul
    co
    #
    @28
    @2
    @5
    @43
    ce
    @33
    @0
    @1
    @5
    @43
    wceq
    ax-icn
    ci
    cA
    cB
    adddi
    mp3an1
    fveq2d
    @2
    @41
    cc
    wcel
    #
    @42
    cc
    wcel
    #
    @44
    @47
    wceq
    @2
    @33
    @0
    @48
    ax-icn
    @0
    @1
    simpl
    #
    ci
    cA
    mulcl
    sylancr
    @2
    @33
    @1
    @49
    ax-icn
    @0
    @1
    simpr
    #
    ci
    cB
    mulcl
    sylancr
    @41
    @42
    efadd
    syl2anc
    @2
    @47
    @12
    @18
    caddc
    co
    #
    @13
    @16
    caddc
    co
    #
    cmul
    co
    @28
    @0
    @1
    @45
    @52
    @46
    @53
    cmul
    cA
    efival
    cB
    efival
    oveqan12d
    @2
    @12
    @18
    @13
    @16
    @30
    @39
    @31
    @36
    muladdd
    eqtrd
    3eqtrd
    @2
    @9
    @7
    cA
    cmul
    co
    #
    @7
    cB
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    @54
    ce
    cfv
    #
    @55
    ce
    cfv
    #
    cmul
    co
    #
    @29
    @2
    @8
    @56
    ce
    @7
    cc
    wcel
    #
    @0
    @1
    @8
    @56
    wceq
    negicn
    @7
    cA
    cB
    adddi
    mp3an1
    fveq2d
    @2
    @54
    cc
    wcel
    #
    @55
    cc
    wcel
    #
    @57
    @60
    wceq
    @2
    @61
    @0
    @62
    negicn
    @50
    @7
    cA
    mulcl
    sylancr
    @2
    @61
    @1
    @63
    negicn
    @51
    @7
    cB
    mulcl
    sylancr
    @54
    @55
    efadd
    syl2anc
    @2
    @60
    @12
    @18
    cmin
    co
    #
    @13
    @16
    cmin
    co
    #
    cmul
    co
    @29
    @0
    @1
    @58
    @64
    @59
    @65
    cmul
    cA
    efmival
    cB
    efmival
    oveqan12d
    @2
    @12
    @18
    @13
    @16
    @30
    @39
    @31
    @36
    mulsubd
    eqtrd
    3eqtrd
    oveq12d
    @2
    @20
    @40
    2timesd
    3eqtr4d
    oveq1d
    @2
    @22
    @20
    @14
    @23
    cneg
    #
    caddc
    co
    @24
    @2
    @20
    cc
    wcel
    #
    @22
    @20
    wceq
    #
    @40
    @67
    c2
    cc
    wcel
    c2
    cc0
    wne
    @68
    2cn
    2ne0
    @20
    c2
    divcan3
    mp3an23
    syl
    @2
    @19
    @66
    @14
    caddc
    @2
    @19
    ci
    ci
    cmul
    co
    #
    @15
    @17
    cmul
    co
    #
    cmul
    co
    #
    c1
    cneg
    #
    @23
    cmul
    co
    #
    @66
    @2
    ci
    @15
    ci
    @17
    @33
    @2
    ax-icn
    a1i
    #
    @35
    @74
    @38
    mul4d
    @2
    @71
    @72
    @70
    cmul
    co
    @73
    @69
    @72
    @70
    cmul
    ixi
    oveq1i
    @2
    @70
    @23
    @72
    cmul
    @2
    @15
    @17
    @35
    @38
    mulcomd
    oveq2d
    syl5eq
    @2
    @23
    @2
    @17
    @15
    @38
    @35
    mulcld
    #
    mulm1d
    3eqtrd
    oveq2d
    @2
    @14
    @23
    @32
    @75
    negsubd
    3eqtrd
    3eqtrd
end
