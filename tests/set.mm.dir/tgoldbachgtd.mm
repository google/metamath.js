include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cc0.mm"
include "c7.mm"
include "c9.mm"
include "c5.mm"
include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "wral.mm"
include "c4.mm"
include "c2.mm"
include "c8.mm"
include "cexp.mm"
include "cmul.mm"
include "cioo.mm"
include "cvma.mm"
include "cof.mm"
include "cvts.mm"
include "ci.mm"
include "cpi.mm"
include "cneg.mm"
include "ce.mm"
include "citg.mm"
include "w3a.mm"
include "cprime.mm"
include "cin.mm"
include "c3.mm"
include "crepr.mm"
include "chash.mm"
include "clt.mm"
include "cpnf.mm"
include "cico.mm"
include "cmap.mm"
include "wcel.mm"
include "wa.mm"
include "ad3antrrr.mm"
include "cdc.mm"
include "wf.mm"
include "elmapi.mm"
include "ad3antlr.mm"
include "ad2antlr.mm"
include "simpr1.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "simpr2.mm"
include "simpr3.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "cbvitgv.mm"
include "syl6breq.mm"
include "tgoldbachgtda.mm"
include "hgt749d.mm"
include "r19.29vva.mm"

theorem tgoldbachgtd
  let wph: wff ph
  let vz: setvar z
  let cN: class N
  let cO: class O
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume tgoldbachgtd.o: |- O = { z e. ZZ | -. 2 || z }
  assume tgoldbachgtd.n: |- ( ph -> N e. O )
  assume tgoldbachgtd.1: |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N )

  disjoint N z
  disjoint O z
  disjoint N h
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint O h
  disjoint O k
  disjoint O m
  disjoint O n
  disjoint h ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> 0 < ( # ` ( ( O i^i Prime ) ( repr ` 3 ) N ) ) )

  proof
    wph
    vm
    cv
    #
    vk
    cv
    #
    cfv
    #
    c1
    cc0
    c7
    c9
    c9
    c5
    c5
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp
    co
    #
    cle
    wbr
    #
    vm
    cn
    wral
    #
    @0
    vh
    cv
    #
    cfv
    #
    c1
    c4
    c1
    c4
    cdp2
    cdp2
    cdp
    co
    #
    cle
    wbr
    #
    vm
    cn
    wral
    #
    cc0
    cc0
    cc0
    cc0
    c4
    c2
    c2
    c4
    c8
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp2
    cdp
    co
    cN
    c2
    cexp
    co
    cmul
    co
    #
    vx
    cc0
    c1
    cioo
    co
    #
    vx
    cv
    #
    cvma
    @6
    cmul
    cof
    #
    co
    cN
    cvts
    co
    #
    cfv
    #
    @13
    cvma
    @1
    @14
    co
    cN
    cvts
    co
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    #
    cN
    cneg
    #
    @13
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    citg
    #
    cle
    wbr
    #
    w3a
    #
    cc0
    cO
    cprime
    cin
    cN
    c3
    crepr
    cfv
    co
    chash
    cfv
    clt
    wbr
    vh
    vk
    cc0
    cpnf
    cico
    co
    #
    cn
    cmap
    co
    #
    @31
    wph
    @6
    @31
    wcel
    #
    wa
    #
    @1
    @31
    wcel
    #
    wa
    #
    @29
    wa
    #
    vy
    vz
    vn
    @6
    @1
    cN
    cO
    tgoldbachgtd.o
    wph
    cN
    cO
    wcel
    @32
    @34
    @29
    tgoldbachgtd.n
    ad3antrrr
    wph
    c1
    cc0
    cdc
    c2
    c7
    cdc
    cexp
    co
    cN
    cle
    wbr
    @32
    @34
    @29
    tgoldbachgtd.1
    ad3antrrr
    @32
    cn
    @30
    @6
    wf
    wph
    @34
    @29
    @6
    @30
    cn
    elmapi
    ad3antlr
    @34
    cn
    @30
    @1
    wf
    @33
    @29
    @1
    @30
    cn
    elmapi
    ad2antlr
    @36
    vn
    cv
    #
    @1
    cfv
    #
    @3
    cle
    wbr
    #
    vn
    cn
    @36
    @5
    @39
    vn
    cn
    wral
    @35
    @5
    @10
    @28
    simpr1
    @4
    @39
    vm
    vn
    cn
    @0
    @37
    wceq
    #
    @2
    @38
    @3
    cle
    @0
    @37
    @1
    fveq2
    breq1d
    cbvralv
    sylib
    r19.21bi
    @36
    @37
    @6
    cfv
    #
    @8
    cle
    wbr
    #
    vn
    cn
    @36
    @10
    @42
    vn
    cn
    wral
    @35
    @5
    @10
    @28
    simpr2
    @9
    @42
    vm
    vn
    cn
    @40
    @7
    @41
    @8
    cle
    @0
    @37
    @6
    fveq2
    breq1d
    cbvralv
    sylib
    r19.21bi
    @36
    @11
    @27
    vy
    @12
    vy
    cv
    #
    @15
    cfv
    #
    @43
    @17
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    @21
    @22
    @43
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    citg
    cle
    @35
    @5
    @10
    @28
    simpr3
    vx
    vy
    @12
    @26
    @51
    @13
    @43
    wceq
    #
    @20
    @47
    @25
    @50
    cmul
    @52
    @16
    @44
    @19
    @46
    cmul
    @13
    @43
    @15
    fveq2
    @52
    @18
    @45
    c2
    cexp
    @13
    @43
    @17
    fveq2
    oveq1d
    oveq12d
    @52
    @24
    @49
    ce
    @52
    @23
    @48
    @21
    cmul
    @13
    @43
    @22
    cmul
    oveq2
    oveq2d
    fveq2d
    oveq12d
    cbvitgv
    syl6breq
    tgoldbachgtda
    wph
    vx
    vz
    vh
    vk
    vm
    cN
    cO
    tgoldbachgtd.o
    tgoldbachgtd.n
    tgoldbachgtd.1
    hgt749d
    r19.29vva
end
