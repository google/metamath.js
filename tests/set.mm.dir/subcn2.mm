include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "caddc.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "negcl.mm"
include "addcn2.mm"
include "syl3an3.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "adantl.mm"
include "simpr.mm"
include "simpll3.mm"
include "neg2subd.mm"
include "abssubd.mm"
include "eqtrd.mm"
include "negsub.mm"
include "adantll.mm"
include "simpll2.mm"
include "negsubd.mm"
include "oveq12d.mm"
include "sylibd.mm"
include "ralrimdva.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"

theorem subcn2
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let cT: class T

  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint u w
  disjoint v w
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint T y
  disjoint T z
  assert |- ( ( A e. RR+ /\ B e. CC /\ C e. CC ) -> E. y e. RR+ E. z e. RR+ A. u e. CC A. v e. CC ( ( ( abs ` ( u - B ) ) < y /\ ( abs ` ( v - C ) ) < z ) -> ( abs ` ( ( u - v ) - ( B - C ) ) ) < A ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    vu
    cv
    #
    cB
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    #
    vw
    cv
    #
    cC
    cneg
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
    wa
    #
    @4
    @6
    caddc
    co
    #
    cB
    @7
    caddc
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    clt
    wbr
    #
    wi
    #
    vw
    cc
    wral
    #
    vu
    cc
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wrex
    #
    @5
    vv
    cv
    #
    cC
    cmin
    co
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    wa
    #
    @4
    @23
    cmin
    co
    #
    cB
    cC
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    clt
    wbr
    #
    wi
    #
    vv
    cc
    wral
    #
    vu
    cc
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wrex
    @2
    @0
    @1
    @7
    cc
    wcel
    @22
    cC
    negcl
    vy
    vz
    vw
    vu
    cA
    cB
    @7
    addcn2
    syl3an3
    @3
    @21
    @35
    vy
    crp
    @3
    @20
    @34
    vz
    crp
    @3
    @19
    @33
    vu
    cc
    @3
    @4
    cc
    wcel
    #
    wa
    #
    @19
    @32
    vv
    cc
    @37
    @23
    cc
    wcel
    #
    wa
    #
    @19
    @5
    @23
    cneg
    #
    @7
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
    wa
    #
    @4
    @40
    caddc
    co
    #
    @14
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    clt
    wbr
    #
    wi
    #
    @32
    @38
    @19
    @49
    wi
    #
    @37
    @38
    @40
    cc
    wcel
    @50
    @23
    negcl
    @18
    @49
    vw
    @40
    cc
    @6
    @40
    wceq
    #
    @12
    @44
    @17
    @48
    @51
    @11
    @43
    @5
    @51
    @9
    @42
    @10
    clt
    @51
    @8
    @41
    cabs
    @6
    @40
    @7
    cmin
    oveq1
    fveq2d
    breq1d
    anbi2d
    @51
    @16
    @47
    cA
    clt
    @51
    @15
    @46
    cabs
    @51
    @13
    @45
    @14
    cmin
    @6
    @40
    @4
    caddc
    oveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl
    adantl
    @39
    @44
    @26
    @48
    @31
    @39
    @43
    @25
    @5
    @39
    @42
    @24
    @10
    clt
    @39
    @42
    cC
    @23
    cmin
    co
    #
    cabs
    cfv
    @24
    @39
    @41
    @52
    cabs
    @39
    @23
    cC
    @37
    @38
    simpr
    #
    @0
    @1
    @2
    @36
    @38
    simpll3
    #
    neg2subd
    fveq2d
    @39
    cC
    @23
    @54
    @53
    abssubd
    eqtrd
    breq1d
    anbi2d
    @39
    @47
    @30
    cA
    clt
    @39
    @46
    @29
    cabs
    @39
    @45
    @27
    @14
    @28
    cmin
    @36
    @38
    @45
    @27
    wceq
    @3
    @4
    @23
    negsub
    adantll
    @39
    cB
    cC
    @0
    @1
    @2
    @36
    @38
    simpll2
    @54
    negsubd
    oveq12d
    fveq2d
    breq1d
    imbi12d
    sylibd
    ralrimdva
    ralimdva
    reximdv
    reximdv
    mpd
end
