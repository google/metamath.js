include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cv.mm"
include "cin.mm"
include "cfn.mm"
include "wdisj.mm"
include "cdif.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "eleq2.mm"
include "pweq.mm"
include "rexeqdv.mm"
include "anbi12d.mm"
include "raleqbi1dv.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem issros
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cS: class S
  let cN: class N
  let cO: class O
  let vs: setvar s
  let cA: class A
  let cB: class B
  assume issros.1: |- N = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x i^i y ) e. s /\ E. z e. ~P s ( z e. Fin /\ Disj_ t e. z t /\ ( x \ y ) = U. z ) ) ) }

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint O s
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint s z
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( S e. N <-> ( S e. ~P ~P O /\ (/) e. S /\ A. x e. S A. y e. S ( ( x i^i y ) e. S /\ E. z e. ~P S ( z e. Fin /\ Disj_ t e. z t /\ ( x \ y ) = U. z ) ) ) )

  proof
    cS
    cN
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
    cin
    #
    cS
    wcel
    #
    vz
    cv
    #
    cfn
    wcel
    vt
    @7
    vt
    cv
    wdisj
    @3
    @4
    cdif
    @7
    cuni
    wceq
    w3a
    #
    vz
    cS
    cpw
    #
    wrex
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
    @13
    w3a
    c0
    vs
    cv
    #
    wcel
    #
    @5
    @15
    wcel
    #
    @8
    vz
    @15
    cpw
    #
    wrex
    #
    wa
    #
    vy
    @15
    wral
    #
    vx
    @15
    wral
    #
    wa
    @14
    vs
    cS
    @0
    cN
    @15
    cS
    wceq
    #
    @16
    @2
    @22
    @13
    @15
    cS
    c0
    eleq2
    @21
    @12
    vx
    @15
    cS
    @20
    @11
    vy
    @15
    cS
    @23
    @17
    @6
    @19
    @10
    @15
    cS
    @5
    eleq2
    @23
    @8
    vz
    @18
    @9
    @15
    cS
    pweq
    rexeqdv
    anbi12d
    raleqbi1dv
    raleqbi1dv
    anbi12d
    issros.1
    elrab2
    @1
    @2
    @13
    3anass
    bitr4i
end
