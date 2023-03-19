include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cuz.mm"
include "cbl.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cdm.mm"
include "cc.mm"
include "cpm.mm"
include "crab.mm"
include "crn.mm"
include "cuni.mm"
include "cca.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-cau.mm"
include "a1i.mm"
include "wa.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "cxp.mm"
include "cxr.mm"
include "xmetf.mm"
include "fdm.mm"
include "syl.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "simpr.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "feq3d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmptd.mm"

theorem caufval
  let vx: setvar x
  let cD: class D
  let vf: setvar f
  let vk: setvar k
  let cX: class X
  let vd: setvar d
  let vj: setvar j
  let vm: setvar m
  let cF: class F
  let wph: wff ph
  let cM: class M
  let cZ: class Z

  disjoint f k
  disjoint f x
  disjoint D f
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint X f
  disjoint X k
  disjoint X x
  disjoint d f
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint D d
  disjoint f j
  disjoint f m
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint D j
  disjoint k m
  disjoint m x
  disjoint D m
  disjoint F f
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint X d
  disjoint X j
  disjoint X m
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  assert |- ( D e. ( *Met ` X ) -> ( Cau ` D ) = { f e. ( X ^pm CC ) | A. x e. RR+ E. k e. ZZ ( f |` ( ZZ>= ` k ) ) : ( ZZ>= ` k ) --> ( ( f ` k ) ( ball ` D ) x ) } )

  proof
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    vd
    cD
    vk
    cv
    #
    cuz
    cfv
    #
    @2
    vf
    cv
    #
    cfv
    #
    vx
    cv
    #
    vd
    cv
    #
    cbl
    cfv
    #
    co
    #
    @4
    @3
    cres
    #
    wf
    #
    vk
    cz
    wrex
    #
    vx
    crp
    wral
    #
    vf
    @7
    cdm
    #
    cdm
    #
    cc
    cpm
    co
    #
    crab
    #
    @3
    @5
    @6
    cD
    cbl
    cfv
    #
    co
    #
    @10
    wf
    #
    vk
    cz
    wrex
    #
    vx
    crp
    wral
    #
    vf
    cX
    cc
    cpm
    co
    #
    crab
    #
    cxmt
    crn
    cuni
    #
    cca
    cvv
    cca
    vd
    @25
    @17
    cmpt
    wceq
    @1
    vx
    vf
    vk
    vd
    df-cau
    a1i
    @1
    @7
    cD
    wceq
    #
    wa
    #
    @13
    @22
    vf
    @16
    @23
    @27
    @15
    cX
    cc
    cpm
    @26
    @1
    @15
    cD
    cdm
    #
    cdm
    #
    cX
    @26
    @14
    @28
    @7
    cD
    dmeq
    dmeqd
    @1
    @29
    cX
    cX
    cxp
    #
    cdm
    cX
    @1
    @28
    @30
    @1
    @30
    cxr
    cD
    wf
    @28
    @30
    wceq
    cD
    cX
    xmetf
    @30
    cxr
    cD
    fdm
    syl
    dmeqd
    cX
    dmxpid
    syl6eq
    sylan9eqr
    oveq1d
    @27
    @12
    @21
    vx
    crp
    @27
    @11
    @20
    vk
    cz
    @27
    @9
    @19
    @10
    @3
    @27
    @8
    @18
    @5
    @6
    @27
    @7
    cD
    cbl
    @1
    @26
    simpr
    fveq2d
    oveqd
    feq3d
    rexbidv
    ralbidv
    rabeqbidv
    @0
    @25
    cD
    cxmt
    cX
    fvssunirn
    sseli
    @24
    cvv
    wcel
    @1
    @22
    vf
    @23
    cX
    cc
    cpm
    ovex
    rabex
    a1i
    fvmptd
end
