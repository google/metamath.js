include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cref.mm"
include "wbr.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "ccref.mm"
include "pweq.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "df-cref.mm"
include "elrab2.mm"

theorem iscref
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cJ: class J
  let cX: class X
  let vj: setvar j
  assume iscref.x: |- X = U. J

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint A j
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint X j
  assert |- ( J e. CovHasRef A <-> ( J e. Top /\ A. y e. ~P J ( X = U. y -> E. z e. ( ~P J i^i A ) z Ref y ) ) )

  proof
    vj
    cv
    #
    cuni
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vz
    cv
    @2
    cref
    wbr
    #
    vz
    @0
    cpw
    #
    cA
    cin
    #
    wrex
    #
    wi
    #
    vy
    @6
    wral
    cX
    @3
    wceq
    #
    @5
    vz
    cJ
    cpw
    #
    cA
    cin
    #
    wrex
    #
    wi
    #
    vy
    @11
    wral
    vj
    cJ
    ctop
    cA
    ccref
    @0
    cJ
    wceq
    #
    @9
    @14
    vy
    @6
    @11
    @0
    cJ
    pweq
    #
    @15
    @4
    @10
    @8
    @13
    @15
    @1
    cX
    @3
    @15
    @1
    cJ
    cuni
    cX
    @0
    cJ
    unieq
    iscref.x
    syl6eqr
    eqeq1d
    @15
    @5
    vz
    @7
    @12
    @15
    @6
    @11
    cA
    @16
    ineq1d
    rexeqdv
    imbi12d
    raleqbidv
    vy
    vz
    cA
    vj
    df-cref
    elrab2
end
