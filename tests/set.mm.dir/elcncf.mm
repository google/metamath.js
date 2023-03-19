include "cc.mm"
include "wss.mm"
include "wa.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cmap.mm"
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
include "wf.mm"
include "crab.mm"
include "cncfval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "ssex.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem elcncf
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
  assert |- ( ( A C_ CC /\ B C_ CC ) -> ( F e. ( A -cn-> B ) <-> ( F : A --> B /\ A. x e. A A. y e. RR+ E. z e. RR+ A. w e. A ( ( abs ` ( x - w ) ) < z -> ( abs ` ( ( F ` x ) - ( F ` w ) ) ) < y ) ) ) )

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
    #
    wcel
    #
    cF
    cB
    cA
    cmap
    co
    #
    wcel
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
    vz
    cv
    clt
    wbr
    #
    @7
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    cmin
    co
    #
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
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    cA
    wral
    #
    wa
    #
    cA
    cB
    cF
    wf
    #
    @18
    wa
    @2
    @4
    cF
    @9
    @7
    vf
    cv
    #
    cfv
    #
    @8
    @21
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @14
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    cA
    wral
    #
    vf
    @5
    crab
    #
    wcel
    @19
    @2
    @3
    @30
    cF
    vx
    vy
    vz
    vw
    cA
    cB
    vf
    cncfval
    eleq2d
    @29
    @18
    vf
    cF
    @5
    @21
    cF
    wceq
    #
    @28
    @17
    vx
    vy
    cA
    crp
    @31
    @27
    @16
    vz
    vw
    crp
    cA
    @31
    @26
    @15
    @9
    @31
    @25
    @13
    @14
    clt
    @31
    @24
    @12
    cabs
    @31
    @22
    @10
    @23
    @11
    cmin
    @7
    @21
    cF
    fveq1
    @8
    @21
    cF
    fveq1
    oveq12d
    fveq2d
    breq1d
    imbi2d
    rexralbidv
    2ralbidv
    elrab
    syl6bb
    @2
    @6
    @20
    @18
    @1
    cB
    cvv
    wcel
    cA
    cvv
    wcel
    @6
    @20
    wb
    @0
    cB
    cc
    cnex
    ssex
    cA
    cc
    cnex
    ssex
    cB
    cA
    cF
    cvv
    cvv
    elmapg
    syl2anr
    anbi1d
    bitrd
end
