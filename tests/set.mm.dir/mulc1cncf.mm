include "cc.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ccncf.mm"
include "cmul.mm"
include "mulcl.mm"
include "fmptd.mm"
include "wa.mm"
include "simprr.mm"
include "simpl.mm"
include "simprl.mm"
include "mulcn2.mm"
include "syl3anc.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "ad2antrr.mm"
include "wb.mm"
include "cc0.mm"
include "subid.mm"
include "abs00bd.mm"
include "simprll.mm"
include "rpgt0d.mm"
include "eqbrtrd.mm"
include "biantrurd.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "simplrl.mm"
include "oveq12d.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "sylibrd.mm"
include "reximdva.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "wss.mm"
include "ssid.mm"
include "elcncf2.mm"
include "mp2an.mm"
include "sylanbrc.mm"

theorem mulc1cncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume mulc1cncf.1: |- F = ( x e. CC |-> ( A x. x ) )

  disjoint A x
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F t
  disjoint F u
  disjoint F w
  disjoint F y
  disjoint F z
  assert |- ( A e. CC -> F e. ( CC -cn-> CC ) )

  proof
    cA
    cc
    wcel
    #
    cc
    cc
    cF
    wf
    #
    vu
    cv
    #
    vy
    cv
    #
    cmin
    co
    cabs
    cfv
    vw
    cv
    #
    clt
    wbr
    #
    @2
    cF
    cfv
    #
    @3
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    wi
    #
    vu
    cc
    wral
    #
    vw
    crp
    wrex
    #
    vz
    crp
    wral
    vy
    cc
    wral
    #
    cF
    cc
    cc
    ccncf
    co
    wcel
    #
    @0
    vx
    cc
    cA
    vx
    cv
    #
    cmul
    co
    #
    cc
    cF
    cA
    @17
    mulcl
    mulc1cncf.1
    fmptd
    @0
    @14
    vy
    vz
    cc
    crp
    @0
    @3
    cc
    wcel
    #
    @10
    crp
    wcel
    #
    wa
    #
    wa
    #
    vv
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vt
    cv
    #
    clt
    wbr
    #
    @5
    wa
    #
    @23
    @2
    cmul
    co
    #
    cA
    @3
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    wi
    #
    vu
    cc
    wral
    #
    vv
    cc
    wral
    #
    vw
    crp
    wrex
    #
    vt
    crp
    wrex
    #
    @14
    @22
    @20
    @0
    @19
    @38
    @0
    @19
    @20
    simprr
    @0
    @21
    simpl
    @0
    @19
    @20
    simprl
    vt
    vw
    vu
    vv
    @10
    cA
    @3
    mulcn2
    syl3anc
    @22
    @37
    @14
    vt
    crp
    @22
    @26
    crp
    wcel
    #
    wa
    @36
    @13
    vw
    crp
    @22
    @39
    @4
    crp
    wcel
    #
    @36
    @13
    wi
    @22
    @39
    @40
    wa
    #
    wa
    #
    @36
    cA
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @26
    clt
    wbr
    #
    @5
    wa
    #
    cA
    @2
    cmul
    co
    #
    @30
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    wi
    #
    vu
    cc
    wral
    #
    @13
    @0
    @36
    @52
    wi
    @21
    @41
    @35
    @52
    vv
    cA
    cc
    @23
    cA
    wceq
    #
    @34
    @51
    vu
    cc
    @53
    @28
    @46
    @33
    @50
    @53
    @27
    @45
    @5
    @53
    @25
    @44
    @26
    clt
    @53
    @24
    @43
    cabs
    @23
    cA
    cA
    cmin
    oveq1
    fveq2d
    breq1d
    anbi1d
    @53
    @32
    @49
    @10
    clt
    @53
    @31
    @48
    cabs
    @53
    @29
    @47
    @30
    cmin
    @23
    cA
    @2
    cmul
    oveq1
    oveq1d
    fveq2d
    breq1d
    imbi12d
    ralbidv
    rspcv
    ad2antrr
    @42
    @12
    @51
    vu
    cc
    @22
    @41
    @2
    cc
    wcel
    #
    @12
    @51
    wb
    @22
    @41
    @54
    wa
    #
    wa
    #
    @5
    @46
    @11
    @50
    @56
    @45
    @5
    @56
    @44
    cc0
    @26
    clt
    @56
    @43
    @0
    @43
    cc0
    wceq
    @21
    @55
    cA
    subid
    ad2antrr
    abs00bd
    @56
    @26
    @22
    @39
    @40
    @54
    simprll
    rpgt0d
    eqbrtrd
    biantrurd
    @56
    @9
    @49
    @10
    clt
    @56
    @8
    @48
    cabs
    @56
    @6
    @47
    @7
    @30
    cmin
    @56
    @54
    @6
    @47
    wceq
    @22
    @41
    @54
    simprr
    vx
    @2
    @18
    @47
    cc
    cF
    @17
    @2
    cA
    cmul
    oveq2
    mulc1cncf.1
    cA
    @2
    cmul
    ovex
    fvmpt
    syl
    @56
    @19
    @7
    @30
    wceq
    @0
    @19
    @20
    @55
    simplrl
    vx
    @3
    @18
    @30
    cc
    cF
    @17
    @3
    cA
    cmul
    oveq2
    mulc1cncf.1
    cA
    @3
    cmul
    ovex
    fvmpt
    syl
    oveq12d
    fveq2d
    breq1d
    imbi12d
    anassrs
    ralbidva
    sylibrd
    anassrs
    reximdva
    rexlimdva
    mpd
    ralrimivva
    cc
    cc
    wss
    #
    @57
    @16
    @1
    @15
    wa
    wb
    cc
    ssid
    #
    @58
    vy
    vz
    vw
    vu
    cc
    cc
    cF
    elcncf2
    mp2an
    sylanbrc
end
