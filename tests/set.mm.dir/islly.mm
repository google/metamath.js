include "cv.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "ctop.mm"
include "clly.mm"
include "wceq.mm"
include "ineq1.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "ralbidv.mm"
include "raleqbi1dv.mm"
include "df-lly.mm"
include "elrab2.mm"

theorem islly
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
  assert |- ( J e. Locally A <-> ( J e. Top /\ A. x e. J A. y e. x E. u e. ( J i^i ~P x ) ( y e. u /\ ( J |`t u ) e. A ) ) )

  proof
    vy
    cv
    vu
    cv
    #
    wcel
    #
    vj
    cv
    #
    @0
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vu
    @2
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
    @6
    wral
    #
    vx
    @2
    wral
    @1
    cJ
    @0
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vu
    cJ
    @7
    cin
    #
    wrex
    #
    vy
    @6
    wral
    #
    vx
    cJ
    wral
    vj
    cJ
    ctop
    cA
    clly
    @10
    @16
    vx
    @2
    cJ
    @2
    cJ
    wceq
    #
    @9
    @15
    vy
    @6
    @17
    @5
    @13
    vu
    @8
    @14
    @2
    cJ
    @7
    ineq1
    @17
    @4
    @12
    @1
    @17
    @3
    @11
    cA
    @2
    cJ
    @0
    crest
    oveq1
    eleq1d
    anbi2d
    rexeqbidv
    ralbidv
    raleqbi1dv
    vx
    vy
    vu
    cA
    vj
    df-lly
    elrab2
end
