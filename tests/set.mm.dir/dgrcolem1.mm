include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "cdgr.mm"
include "cmul.mm"
include "wceq.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "wa.mm"
include "cply.mm"
include "wf.mm"
include "plyf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "exp1d.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "eqtr4d.mm"
include "syl6eqr.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "cof.mm"
include "adantlr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "adantl.mm"
include "adantr.mm"
include "expp1d.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "ovexd.mm"
include "eqidd.mm"
include "offval2.mm"
include "nncn.mm"
include "1cnd.mm"
include "adddird.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "c0p.mm"
include "wne.mm"
include "ccom.mm"
include "fmptco.mm"
include "wss.mm"
include "ssid.mm"
include "plypow.mm"
include "syl3anc.mm"
include "plyssc.mm"
include "sseldi.mm"
include "addcl.mm"
include "mulcl.mm"
include "plyco.mm"
include "eqeltrrd.mm"
include "cc0.mm"
include "simpr.mm"
include "nnmulcld.mm"
include "nnne0d.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl5eq.mm"
include "eqid.mm"
include "dgrmul.mm"
include "syl22anc.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "mpcom.mm"

theorem dgrcolem1
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cG: class G
  let cM: class M
  let cN: class N
  let vd: setvar d
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume dgrcolem1.1: |- N = ( deg ` G )
  assume dgrcolem1.2: |- ( ph -> M e. NN )
  assume dgrcolem1.3: |- ( ph -> N e. NN )
  assume dgrcolem1.4: |- ( ph -> G e. ( Poly ` S ) )

  disjoint G x
  disjoint M x
  disjoint ph x
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint M y
  disjoint N d
  disjoint N y
  disjoint d ph
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( deg ` ( x e. CC |-> ( ( G ` x ) ^ M ) ) ) = ( M x. N ) )

  proof
    cM
    cn
    wcel
    wph
    vx
    cc
    vx
    cv
    #
    cG
    cfv
    #
    cM
    cexp
    co
    #
    cmpt
    #
    cdgr
    cfv
    #
    cM
    cN
    cmul
    co
    #
    wceq
    #
    dgrcolem1.2
    wph
    vx
    cc
    @1
    vy
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cdgr
    cfv
    #
    @7
    cN
    cmul
    co
    #
    wceq
    #
    wi
    wph
    vx
    cc
    @1
    c1
    cexp
    co
    #
    cmpt
    #
    cdgr
    cfv
    #
    c1
    cN
    cmul
    co
    #
    wceq
    #
    wi
    wph
    vx
    cc
    @1
    vd
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cdgr
    cfv
    #
    @18
    cN
    cmul
    co
    #
    wceq
    #
    wi
    wph
    vx
    cc
    @1
    @18
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmpt
    #
    cdgr
    cfv
    #
    @24
    cN
    cmul
    co
    #
    wceq
    #
    wi
    wph
    @6
    wi
    vy
    vd
    cM
    @7
    c1
    wceq
    #
    @12
    @17
    wph
    @30
    @10
    @15
    @11
    @16
    @30
    @9
    @14
    cdgr
    @30
    vx
    cc
    @8
    @13
    @7
    c1
    @1
    cexp
    oveq2
    mpteq2dv
    fveq2d
    @7
    c1
    cN
    cmul
    oveq1
    eqeq12d
    imbi2d
    @7
    @18
    wceq
    #
    @12
    @23
    wph
    @31
    @10
    @21
    @11
    @22
    @31
    @9
    @20
    cdgr
    @31
    vx
    cc
    @8
    @19
    @7
    @18
    @1
    cexp
    oveq2
    mpteq2dv
    fveq2d
    @7
    @18
    cN
    cmul
    oveq1
    eqeq12d
    imbi2d
    @7
    @24
    wceq
    #
    @12
    @29
    wph
    @32
    @10
    @27
    @11
    @28
    @32
    @9
    @26
    cdgr
    @32
    vx
    cc
    @8
    @25
    @7
    @24
    @1
    cexp
    oveq2
    mpteq2dv
    fveq2d
    @7
    @24
    cN
    cmul
    oveq1
    eqeq12d
    imbi2d
    @7
    cM
    wceq
    #
    @12
    @6
    wph
    @33
    @10
    @4
    @11
    @5
    @33
    @9
    @3
    cdgr
    @33
    vx
    cc
    @8
    @2
    @7
    cM
    @1
    cexp
    oveq2
    mpteq2dv
    fveq2d
    @7
    cM
    cN
    cmul
    oveq1
    eqeq12d
    imbi2d
    wph
    @15
    cN
    @16
    wph
    @15
    cG
    cdgr
    cfv
    #
    cN
    wph
    @14
    cG
    cdgr
    wph
    @14
    vx
    cc
    @1
    cmpt
    #
    cG
    wph
    vx
    cc
    @13
    @1
    wph
    @0
    cc
    wcel
    #
    wa
    @1
    wph
    cc
    cc
    @0
    cG
    wph
    cG
    cS
    cply
    cfv
    #
    wcel
    #
    cc
    cc
    cG
    wf
    dgrcolem1.4
    cS
    cG
    plyf
    syl
    #
    ffvelrnda
    #
    exp1d
    mpteq2dva
    wph
    vx
    cc
    cc
    cG
    @39
    feqmptd
    #
    eqtr4d
    fveq2d
    dgrcolem1.1
    syl6eqr
    wph
    cN
    wph
    cN
    dgrcolem1.3
    nncnd
    #
    mulid2d
    eqtr4d
    @18
    cn
    wcel
    #
    wph
    @23
    @29
    wph
    @43
    @23
    @29
    wi
    wph
    @43
    wa
    #
    @23
    @29
    @44
    @23
    wa
    #
    @27
    @20
    cG
    cmul
    cof
    co
    #
    cdgr
    cfv
    #
    @28
    @44
    @27
    @47
    wceq
    @23
    @44
    @26
    @46
    cdgr
    @44
    @26
    vx
    cc
    @19
    @1
    cmul
    co
    #
    cmpt
    @46
    @44
    vx
    cc
    @25
    @48
    @44
    @36
    wa
    #
    @1
    @18
    wph
    @36
    @1
    cc
    wcel
    @43
    @40
    adantlr
    #
    @44
    @18
    cn0
    wcel
    #
    @36
    @43
    @51
    wph
    @18
    nnnn0
    adantl
    #
    adantr
    expp1d
    mpteq2dva
    @44
    vx
    cc
    @19
    @1
    cmul
    @20
    cG
    cvv
    cvv
    cc
    cc
    cvv
    wcel
    @44
    cnex
    a1i
    @49
    @1
    @18
    cexp
    ovexd
    @50
    @44
    @20
    eqidd
    wph
    cG
    @35
    wceq
    @43
    @41
    adantr
    #
    offval2
    eqtr4d
    fveq2d
    adantr
    @45
    @28
    @22
    cN
    caddc
    co
    #
    @47
    @44
    @28
    @54
    wceq
    @23
    @44
    @28
    @22
    @16
    caddc
    co
    @54
    @44
    @18
    c1
    cN
    @43
    @18
    cc
    wcel
    wph
    @18
    nncn
    adantl
    @44
    1cnd
    #
    wph
    cN
    cc
    wcel
    @43
    @42
    adantr
    #
    adddird
    @44
    @16
    cN
    @22
    caddc
    @44
    cN
    @56
    mulid2d
    oveq2d
    eqtrd
    adantr
    @45
    @47
    @21
    cN
    caddc
    co
    #
    @54
    @45
    @20
    cc
    cply
    cfv
    #
    wcel
    #
    @20
    c0p
    wne
    #
    cG
    @58
    wcel
    #
    cG
    c0p
    wne
    #
    @47
    @57
    wceq
    @44
    @59
    @23
    @44
    vy
    cc
    @7
    @18
    cexp
    co
    #
    cmpt
    #
    cG
    ccom
    @20
    @58
    @44
    vx
    vy
    cc
    cc
    @1
    @63
    @19
    cG
    @64
    @50
    @53
    @44
    @64
    eqidd
    @7
    @1
    @18
    cexp
    oveq1
    fmptco
    @44
    vz
    vw
    cc
    @64
    cG
    @44
    cc
    cc
    wss
    #
    c1
    cc
    wcel
    @51
    @64
    @58
    wcel
    @65
    @44
    cc
    ssid
    a1i
    @55
    @52
    vy
    cc
    @18
    plypow
    syl3anc
    @44
    @37
    @58
    cG
    cS
    plyssc
    wph
    @38
    @43
    dgrcolem1.4
    adantr
    sseldi
    #
    vz
    cv
    #
    cc
    wcel
    vw
    cv
    #
    cc
    wcel
    wa
    #
    @67
    @68
    caddc
    co
    cc
    wcel
    @44
    @67
    @68
    addcl
    adantl
    @69
    @67
    @68
    cmul
    co
    cc
    wcel
    @44
    @67
    @68
    mulcl
    adantl
    plyco
    eqeltrrd
    adantr
    @45
    @21
    cc0
    wne
    @60
    @45
    @21
    @22
    cc0
    @44
    @23
    simpr
    @44
    @22
    cc0
    wne
    @23
    @44
    @22
    @44
    @18
    cN
    wph
    @43
    simpr
    wph
    cN
    cn
    wcel
    @43
    dgrcolem1.3
    adantr
    nnmulcld
    nnne0d
    adantr
    eqnetrd
    @20
    c0p
    @21
    cc0
    @20
    c0p
    wceq
    @21
    c0p
    cdgr
    cfv
    #
    cc0
    @20
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    @44
    @61
    @23
    @66
    adantr
    @44
    @62
    @23
    wph
    @62
    @43
    wph
    cN
    cc0
    wne
    @62
    wph
    cN
    dgrcolem1.3
    nnne0d
    cG
    c0p
    cN
    cc0
    cG
    c0p
    wceq
    #
    cN
    @34
    cc0
    dgrcolem1.1
    @71
    @34
    @70
    cc0
    cG
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    syl5eq
    necon3i
    syl
    adantr
    adantr
    cc
    @20
    cG
    @21
    cN
    @21
    eqid
    dgrcolem1.1
    dgrmul
    syl22anc
    @23
    @57
    @54
    wceq
    @44
    @21
    @22
    cN
    caddc
    oveq1
    adantl
    eqtrd
    eqtr4d
    eqtr4d
    ex
    expcom
    a2d
    nnind
    mpcom
end
