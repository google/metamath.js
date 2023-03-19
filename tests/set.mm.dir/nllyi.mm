include "cnlly.mm"
include "wcel.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "ctop.mm"
include "isnlly.mm"
include "simprbi.mm"
include "wceq.mm"
include "pweq.mm"
include "ineq2d.mm"
include "rexeqdv.mm"
include "raleqbi1dv.mm"
include "rspccva.mm"
include "sylan.mm"
include "elin.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "wb.mm"
include "selpw.mm"
include "a1i.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "anass.mm"
include "syl6bb.mm"
include "rexbidv2.mm"
include "stoic3.mm"

theorem nllyi
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
  assert |- ( ( J e. N-Locally A /\ U e. J /\ P e. U ) -> E. u e. ( ( nei ` J ) ` { P } ) ( u C_ U /\ ( J |`t u ) e. A ) )

  proof
    cJ
    cA
    cnlly
    wcel
    #
    cU
    cJ
    wcel
    #
    cJ
    vu
    cv
    #
    crest
    co
    cA
    wcel
    #
    vu
    vy
    cv
    #
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
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
    @2
    cU
    wss
    #
    @3
    wa
    #
    vu
    cP
    csn
    #
    @6
    cfv
    #
    wrex
    #
    @0
    @3
    vu
    @7
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
    @17
    wral
    #
    vx
    cJ
    wral
    #
    @1
    @11
    @0
    cJ
    ctop
    wcel
    @22
    vx
    vy
    vu
    cA
    cJ
    isnlly
    simprbi
    @21
    @11
    vx
    cU
    cJ
    @20
    @10
    vy
    @17
    cU
    @17
    cU
    wceq
    #
    @3
    vu
    @19
    @9
    @23
    @18
    @8
    @7
    @17
    cU
    pweq
    ineq2d
    rexeqdv
    raleqbi1dv
    rspccva
    sylan
    @10
    @16
    vy
    cP
    cU
    @4
    cP
    wceq
    #
    @3
    @13
    vu
    @9
    @15
    @24
    @2
    @9
    wcel
    #
    @3
    wa
    @2
    @15
    wcel
    #
    @12
    wa
    #
    @3
    wa
    @26
    @13
    wa
    @24
    @25
    @27
    @3
    @25
    @2
    @7
    wcel
    #
    @2
    @8
    wcel
    #
    wa
    @24
    @27
    @2
    @7
    @8
    elin
    @24
    @28
    @26
    @29
    @12
    @24
    @7
    @15
    @2
    @24
    @5
    @14
    @6
    @4
    cP
    sneq
    fveq2d
    eleq2d
    @29
    @12
    wb
    @24
    vu
    cU
    selpw
    a1i
    anbi12d
    syl5bb
    anbi1d
    @26
    @12
    @3
    anass
    syl6bb
    rexbidv2
    rspccva
    stoic3
end
