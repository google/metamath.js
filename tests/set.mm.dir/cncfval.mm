include "cc.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "ccncf.mm"
include "co.mm"
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
include "cmap.mm"
include "crab.mm"
include "wceq.mm"
include "cnex.mm"
include "elpw2.mm"
include "oveq2.mm"
include "raleq.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "raleqbi1dv.mm"
include "rabeqbidv.mm"
include "oveq1.mm"
include "rabeq.mm"
include "syl.mm"
include "df-cncf.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "syl2anbr.mm"

theorem cncfval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let cF: class F
  let cR: class R

  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
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
  disjoint B f
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
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F f
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint B a
  disjoint B b
  assert |- ( ( A C_ CC /\ B C_ CC ) -> ( A -cn-> B ) = { f e. ( B ^m A ) | A. x e. A A. y e. RR+ E. z e. RR+ A. w e. A ( ( abs ` ( x - w ) ) < z -> ( abs ` ( ( f ` x ) - ( f ` w ) ) ) < y ) } )

  proof
    cA
    cc
    wss
    cA
    cc
    cpw
    #
    wcel
    cB
    @0
    wcel
    cA
    cB
    ccncf
    co
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
    @1
    vf
    cv
    #
    cfv
    @2
    @3
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
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
    vf
    cB
    cA
    cmap
    co
    #
    crab
    #
    wceq
    cB
    cc
    wss
    cA
    cc
    cnex
    elpw2
    cB
    cc
    cnex
    elpw2
    va
    vb
    cA
    cB
    @0
    @0
    @4
    vw
    va
    cv
    #
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
    @11
    wral
    #
    vf
    vb
    cv
    #
    @11
    cmap
    co
    #
    crab
    @10
    ccncf
    @8
    vf
    @16
    cA
    cmap
    co
    #
    crab
    #
    @11
    cA
    wceq
    #
    @15
    @8
    vf
    @17
    @18
    @11
    cA
    @16
    cmap
    oveq2
    @14
    @7
    vx
    @11
    cA
    @20
    @13
    @6
    vy
    crp
    @20
    @12
    @5
    vz
    crp
    @4
    vw
    @11
    cA
    raleq
    rexbidv
    ralbidv
    raleqbi1dv
    rabeqbidv
    @16
    cB
    wceq
    @18
    @9
    wceq
    @19
    @10
    wceq
    @16
    cB
    cA
    cmap
    oveq1
    @8
    vf
    @18
    @9
    rabeq
    syl
    vx
    vw
    vy
    vf
    va
    vb
    vz
    df-cncf
    @8
    vf
    @9
    cB
    cA
    cmap
    ovex
    rabex
    ovmpt2
    syl2anbr
end
