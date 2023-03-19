include "con0.mm"
include "wss.mm"
include "com.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "wf1.mm"
include "simplr.mm"
include "wo.mm"
include "wn.mm"
include "omsmolem.mm"
include "adantl.mm"
include "imp.mm"
include "adantr.mm"
include "orim12d.mm"
include "ancoms.mm"
include "con3d.mm"
include "wb.mm"
include "word.mm"
include "ffvelrn.mm"
include "ssel.mm"
include "syl5.mm"
include "expdimp.mm"
include "eloni.mm"
include "syl6.mm"
include "anim12d.mm"
include "ordtri3.mm"
include "syl.mm"
include "adantlr.mm"
include "nnord.mm"
include "syl2an.mm"
include "3imtr4d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem omsmo
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint F x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint F y
  disjoint F z
  disjoint F w
  assert |- ( ( ( A C_ On /\ F : _om --> A ) /\ A. x e. _om ( F ` x ) e. ( F ` suc x ) ) -> F : _om -1-1-> A )

  proof
    cA
    con0
    wss
    #
    com
    cA
    cF
    wf
    #
    wa
    #
    vx
    cv
    #
    cF
    cfv
    @3
    csuc
    cF
    cfv
    wcel
    vx
    com
    wral
    #
    wa
    #
    @1
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @6
    @8
    wceq
    #
    wi
    #
    vz
    com
    wral
    vy
    com
    wral
    com
    cA
    cF
    wf1
    @0
    @1
    @4
    simplr
    @5
    @12
    vy
    vz
    com
    com
    @5
    @6
    com
    wcel
    #
    @8
    com
    wcel
    #
    wa
    #
    wa
    #
    @7
    @9
    wcel
    #
    @9
    @7
    wcel
    #
    wo
    #
    wn
    #
    @6
    @8
    wcel
    #
    @8
    @6
    wcel
    #
    wo
    #
    wn
    #
    @10
    @11
    @16
    @23
    @19
    @15
    @5
    @23
    @19
    wi
    @15
    @5
    wa
    @21
    @17
    @22
    @18
    @15
    @5
    @21
    @17
    wi
    #
    @14
    @5
    @25
    wi
    @13
    vx
    vz
    vy
    cA
    cF
    omsmolem
    adantl
    imp
    @15
    @5
    @22
    @18
    wi
    #
    @13
    @5
    @26
    wi
    @14
    vx
    vy
    vz
    cA
    cF
    omsmolem
    adantr
    imp
    orim12d
    ancoms
    con3d
    @2
    @15
    @10
    @20
    wb
    #
    @4
    @2
    @15
    wa
    @7
    word
    #
    @9
    word
    #
    wa
    #
    @27
    @2
    @15
    @30
    @2
    @13
    @28
    @14
    @29
    @2
    @13
    @7
    con0
    wcel
    #
    @28
    @0
    @1
    @13
    @31
    @1
    @13
    wa
    @7
    cA
    wcel
    @0
    @31
    com
    cA
    @6
    cF
    ffvelrn
    cA
    con0
    @7
    ssel
    syl5
    expdimp
    @7
    eloni
    syl6
    @2
    @14
    @9
    con0
    wcel
    #
    @29
    @0
    @1
    @14
    @32
    @1
    @14
    wa
    @9
    cA
    wcel
    @0
    @32
    com
    cA
    @8
    cF
    ffvelrn
    cA
    con0
    @9
    ssel
    syl5
    expdimp
    @9
    eloni
    syl6
    anim12d
    imp
    @7
    @9
    ordtri3
    syl
    adantlr
    @15
    @11
    @24
    wb
    #
    @5
    @13
    @6
    word
    @8
    word
    @33
    @14
    @6
    nnord
    @8
    nnord
    @6
    @8
    ordtri3
    syl2an
    adantl
    3imtr4d
    ralrimivva
    vy
    vz
    com
    cA
    cF
    dff13
    sylanbrc
end
