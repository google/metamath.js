include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "cv.mm"
include "cfn.mm"
include "wdisj.mm"
include "cdif.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "simp2.mm"
include "simp3.mm"
include "c0.mm"
include "issros.mm"
include "simp3bi.mm"
include "3ad2ant1.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "difeq1.mm"
include "eqeq1d.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "ineq2.mm"
include "difeq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "simprd.mm"

theorem diffiunisros
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cS: class S
  let cN: class N
  let cO: class O
  let vs: setvar s
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
  assert |- ( ( S e. N /\ A e. S /\ B e. S ) -> E. z e. ~P S ( z e. Fin /\ Disj_ t e. z t /\ ( A \ B ) = U. z ) )

  proof
    cS
    cN
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    #
    cA
    cB
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
    #
    vt
    @6
    vt
    cv
    wdisj
    #
    cA
    cB
    cdif
    #
    @6
    cuni
    #
    wceq
    #
    w3a
    #
    vz
    cS
    cpw
    #
    wrex
    #
    @3
    @1
    @2
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
    @7
    @8
    @15
    @16
    cdif
    #
    @10
    wceq
    #
    w3a
    #
    vz
    @13
    wrex
    #
    wa
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @5
    @14
    wa
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @0
    @1
    @24
    @2
    @0
    cS
    cO
    cpw
    cpw
    wcel
    c0
    cS
    wcel
    @24
    vx
    vy
    vz
    vt
    cS
    cN
    cO
    vs
    issros.1
    issros
    simp3bi
    3ad2ant1
    @23
    @25
    cA
    @16
    cin
    #
    cS
    wcel
    #
    @7
    @8
    cA
    @16
    cdif
    #
    @10
    wceq
    #
    w3a
    #
    vz
    @13
    wrex
    #
    wa
    vx
    vy
    cA
    cB
    cS
    cS
    @15
    cA
    wceq
    #
    @18
    @27
    @22
    @31
    @32
    @17
    @26
    cS
    @15
    cA
    @16
    ineq1
    eleq1d
    @32
    @21
    @30
    vz
    @13
    @32
    @20
    @29
    @7
    @8
    @32
    @19
    @28
    @10
    @15
    cA
    @16
    difeq1
    eqeq1d
    3anbi3d
    rexbidv
    anbi12d
    @16
    cB
    wceq
    #
    @27
    @5
    @31
    @14
    @33
    @26
    @4
    cS
    @16
    cB
    cA
    ineq2
    eleq1d
    @33
    @30
    @12
    vz
    @13
    @33
    @29
    @11
    @7
    @8
    @33
    @28
    @9
    @10
    @16
    cB
    cA
    difeq2
    eqeq1d
    3anbi3d
    rexbidv
    anbi12d
    rspc2va
    syl21anc
    simprd
end
