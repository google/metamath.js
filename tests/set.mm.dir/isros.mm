include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cv.mm"
include "cun.mm"
include "cdif.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "wceq.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "raleqbi1dv.mm"
include "elrab2.mm"
include "3anass.mm"
include "uneq1.mm"
include "eleq1d.mm"
include "difeq1.mm"
include "uneq2.mm"
include "difeq2.mm"
include "cbvral2v.mm"
include "3anbi3i.mm"
include "3bitr2i.mm"

theorem isros
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cQ: class Q
  let cS: class S
  let cO: class O
  let vs: setvar s
  let cA: class A
  let cB: class B
  assume isros.1: |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) }

  disjoint u v
  disjoint O s
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint A u
  disjoint A v
  disjoint B u
  disjoint B v
  assert |- ( S e. Q <-> ( S e. ~P ~P O /\ (/) e. S /\ A. u e. S A. v e. S ( ( u u. v ) e. S /\ ( u \ v ) e. S ) ) )

  proof
    cS
    cQ
    wcel
    cS
    cO
    cpw
    cpw
    #
    wcel
    #
    c0
    cS
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cS
    wcel
    #
    @3
    @4
    cdif
    #
    cS
    wcel
    #
    wa
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    wa
    #
    wa
    @1
    @2
    @11
    w3a
    @1
    @2
    vu
    cv
    #
    vv
    cv
    #
    cun
    #
    cS
    wcel
    #
    @13
    @14
    cdif
    #
    cS
    wcel
    #
    wa
    #
    vv
    cS
    wral
    vu
    cS
    wral
    #
    w3a
    c0
    vs
    cv
    #
    wcel
    #
    @5
    @21
    wcel
    #
    @7
    @21
    wcel
    #
    wa
    #
    vy
    @21
    wral
    #
    vx
    @21
    wral
    #
    wa
    @12
    vs
    cS
    @0
    cQ
    @21
    cS
    wceq
    #
    @22
    @2
    @27
    @11
    @21
    cS
    c0
    eleq2
    @26
    @10
    vx
    @21
    cS
    @25
    @9
    vy
    @21
    cS
    @28
    @23
    @6
    @24
    @8
    @21
    cS
    @5
    eleq2
    @21
    cS
    @7
    eleq2
    anbi12d
    raleqbi1dv
    raleqbi1dv
    anbi12d
    isros.1
    elrab2
    @1
    @2
    @11
    3anass
    @11
    @20
    @1
    @2
    @9
    @19
    @13
    @4
    cun
    #
    cS
    wcel
    #
    @13
    @4
    cdif
    #
    cS
    wcel
    #
    wa
    vx
    vy
    vu
    vv
    cS
    cS
    @3
    @13
    wceq
    #
    @6
    @30
    @8
    @32
    @33
    @5
    @29
    cS
    @3
    @13
    @4
    uneq1
    eleq1d
    @33
    @7
    @31
    cS
    @3
    @13
    @4
    difeq1
    eleq1d
    anbi12d
    @4
    @14
    wceq
    #
    @30
    @16
    @32
    @18
    @34
    @29
    @15
    cS
    @4
    @14
    @13
    uneq2
    eleq1d
    @34
    @31
    @17
    cS
    @4
    @14
    @13
    difeq2
    eleq1d
    anbi12d
    cbvral2v
    3anbi3i
    3bitr2i
end
