include "cc.mm"
include "wss.mm"
include "wa.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "elcncf.mm"
include "wb.mm"
include "simplll.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "abssubd.mm"
include "breq1d.mm"
include "simpllr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "imbi12d.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem elcncf2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let cC: class C
  let cR: class R

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a f
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b f
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F f
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint B a
  disjoint B b
  disjoint B f
  assert |- ( ( A C_ CC /\ B C_ CC ) -> ( F e. ( A -cn-> B ) <-> ( F : A --> B /\ A. x e. A A. y e. RR+ E. z e. RR+ A. w e. A ( ( abs ` ( w - x ) ) < z -> ( abs ` ( ( F ` w ) - ( F ` x ) ) ) < y ) ) ) )

  proof
    cA
    cc
    wss
    #
    cB
    cc
    wss
    #
    wa
    #
    cF
    cA
    cB
    ccncf
    co
    wcel
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    vw
    cv
    #
    cmin
    co
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    cmin
    co
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    cA
    wral
    #
    wa
    @3
    @5
    @4
    cmin
    co
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @10
    @9
    cmin
    co
    cabs
    cfv
    #
    @12
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    cA
    wral
    #
    wa
    vx
    vy
    vz
    vw
    cA
    cB
    cF
    elcncf
    @2
    @3
    @18
    @27
    @2
    @3
    wa
    #
    @17
    @26
    vx
    cA
    @28
    @4
    cA
    wcel
    #
    wa
    #
    @16
    @25
    vy
    crp
    @30
    @15
    @24
    vz
    crp
    @30
    @14
    @23
    vw
    cA
    @28
    @29
    @5
    cA
    wcel
    #
    @14
    @23
    wb
    @28
    @29
    @31
    wa
    #
    wa
    #
    @8
    @20
    @13
    @22
    @33
    @6
    @19
    @7
    clt
    @33
    @4
    @5
    @33
    cA
    cc
    @4
    @0
    @1
    @3
    @32
    simplll
    #
    @28
    @29
    @31
    simprl
    #
    sseldd
    @33
    cA
    cc
    @5
    @34
    @28
    @29
    @31
    simprr
    #
    sseldd
    abssubd
    breq1d
    @33
    @11
    @21
    @12
    clt
    @33
    @9
    @10
    @33
    cB
    cc
    @9
    @0
    @1
    @3
    @32
    simpllr
    #
    @33
    cA
    cB
    @4
    cF
    @2
    @3
    @32
    simplr
    #
    @35
    ffvelrnd
    sseldd
    @33
    cB
    cc
    @10
    @37
    @33
    cA
    cB
    @5
    cF
    @38
    @36
    ffvelrnd
    sseldd
    abssubd
    breq1d
    imbi12d
    anassrs
    ralbidva
    rexbidv
    ralbidv
    ralbidva
    pm5.32da
    bitrd
end
