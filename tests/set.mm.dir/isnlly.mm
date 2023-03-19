include "cv.mm"
include "crest.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "ctop.mm"
include "cnlly.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "ineq1d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rexeqbidv.mm"
include "ralbidv.mm"
include "raleqbi1dv.mm"
include "df-nlly.mm"
include "elrab2.mm"

theorem isnlly
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cJ: class J
  let vj: setvar j
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cP: class P
  let cU: class U
  let cV: class V

  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint j s
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u w
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B j
  disjoint B u
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P s
  disjoint P u
  disjoint P y
  disjoint U s
  disjoint U u
  disjoint U x
  disjoint U y
  disjoint J j
  disjoint J s
  disjoint J w
  disjoint J z
  disjoint V u
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( J e. N-Locally A <-> ( J e. Top /\ A. x e. J A. y e. x E. u e. ( ( ( nei ` J ) ` { y } ) i^i ~P x ) ( J |`t u ) e. A ) )

  proof
    vj
    cv
    #
    vu
    cv
    #
    crest
    co
    #
    cA
    wcel
    #
    vu
    vy
    cv
    csn
    #
    @0
    cnei
    cfv
    #
    cfv
    #
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @7
    wral
    #
    vx
    @0
    wral
    cJ
    @1
    crest
    co
    #
    cA
    wcel
    #
    vu
    @4
    cJ
    cnei
    cfv
    #
    cfv
    #
    @8
    cin
    #
    wrex
    #
    vy
    @7
    wral
    #
    vx
    cJ
    wral
    vj
    cJ
    ctop
    cA
    cnlly
    @11
    @18
    vx
    @0
    cJ
    @0
    cJ
    wceq
    #
    @10
    @17
    vy
    @7
    @19
    @3
    @13
    vu
    @9
    @16
    @19
    @6
    @15
    @8
    @19
    @4
    @5
    @14
    @0
    cJ
    cnei
    fveq2
    fveq1d
    ineq1d
    @19
    @2
    @12
    cA
    @0
    cJ
    @1
    crest
    oveq1
    eleq1d
    rexeqbidv
    ralbidv
    raleqbi1dv
    vx
    vy
    vu
    cA
    vj
    df-nlly
    elrab2
end
