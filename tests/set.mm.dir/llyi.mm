include "clly.mm"
include "wcel.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "wss.mm"
include "w3a.mm"
include "ctop.mm"
include "islly.mm"
include "simprbi.mm"
include "wceq.mm"
include "pweq.mm"
include "ineq2d.mm"
include "rexeqdv.mm"
include "raleqbi1dv.mm"
include "rspccva.mm"
include "sylan.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "anass.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "anbi1i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "syl6bb.mm"
include "rexbidv2.mm"
include "stoic3.mm"

theorem llyi
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cU: class U
  let cJ: class J
  let vj: setvar j
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V

  disjoint A u
  disjoint P u
  disjoint U u
  disjoint J u
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
  disjoint u x
  disjoint u y
  disjoint u z
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
  disjoint B j
  disjoint B u
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P s
  disjoint P y
  disjoint U s
  disjoint U x
  disjoint U y
  disjoint J j
  disjoint J s
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V u
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( J e. Locally A /\ U e. J /\ P e. U ) -> E. u e. J ( u C_ U /\ P e. u /\ ( J |`t u ) e. A ) )

  proof
    cJ
    cA
    clly
    wcel
    #
    cU
    cJ
    wcel
    #
    vy
    cv
    #
    vu
    cv
    #
    wcel
    #
    cJ
    @3
    crest
    co
    cA
    wcel
    #
    wa
    #
    vu
    cJ
    cU
    cpw
    #
    cin
    #
    wrex
    #
    vy
    cU
    wral
    #
    cP
    cU
    wcel
    @3
    cU
    wss
    #
    cP
    @3
    wcel
    #
    @5
    w3a
    #
    vu
    cJ
    wrex
    #
    @0
    @6
    vu
    cJ
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
    @15
    wral
    #
    vx
    cJ
    wral
    #
    @1
    @10
    @0
    cJ
    ctop
    wcel
    @20
    vx
    vy
    vu
    cA
    cJ
    islly
    simprbi
    @19
    @10
    vx
    cU
    cJ
    @18
    @9
    vy
    @15
    cU
    @15
    cU
    wceq
    #
    @6
    vu
    @17
    @8
    @21
    @16
    @7
    cJ
    @15
    cU
    pweq
    ineq2d
    rexeqdv
    raleqbi1dv
    rspccva
    sylan
    @9
    @14
    vy
    cP
    cU
    @2
    cP
    wceq
    #
    @6
    @13
    vu
    @8
    cJ
    @22
    @3
    @8
    wcel
    #
    @6
    wa
    @23
    @12
    @5
    wa
    #
    wa
    #
    @3
    cJ
    wcel
    #
    @13
    wa
    #
    @22
    @6
    @24
    @23
    @22
    @4
    @12
    @5
    @2
    cP
    @3
    eleq1
    anbi1d
    anbi2d
    @26
    @11
    wa
    #
    @24
    wa
    @26
    @11
    @24
    wa
    #
    wa
    @25
    @27
    @26
    @11
    @24
    anass
    @23
    @28
    @24
    @23
    @26
    @3
    @7
    wcel
    #
    wa
    @28
    @3
    cJ
    @7
    elin
    @30
    @11
    @26
    vu
    cU
    selpw
    anbi2i
    bitri
    anbi1i
    @13
    @29
    @26
    @11
    @12
    @5
    3anass
    anbi2i
    3bitr4i
    syl6bb
    rexbidv2
    rspccva
    stoic3
end
