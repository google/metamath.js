include "ccref.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "cpw.mm"
include "cv.mm"
include "cref.mm"
include "wbr.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "simp1.mm"
include "simp2.mm"
include "sselpwd.mm"
include "ctop.mm"
include "iscref.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "breq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem crefi
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cJ: class J
  let cX: class X
  let vy: setvar y
  assume crefi.x: |- X = U. J

  disjoint A z
  disjoint J z
  disjoint C z
  disjoint A y
  disjoint y z
  disjoint J y
  disjoint C y
  disjoint X y
  assert |- ( ( J e. CovHasRef A /\ C C_ J /\ X = U. C ) -> E. z e. ( ~P J i^i A ) z Ref C )

  proof
    cJ
    cA
    ccref
    #
    wcel
    #
    cC
    cJ
    wss
    #
    cX
    cC
    cuni
    #
    wceq
    #
    w3a
    #
    cC
    cJ
    cpw
    #
    wcel
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vz
    cv
    #
    @7
    cref
    wbr
    #
    vz
    @6
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
    #
    @4
    @10
    cC
    cref
    wbr
    #
    vz
    @12
    wrex
    #
    @5
    cC
    cJ
    @0
    @1
    @2
    @4
    simp1
    @1
    @2
    @4
    simp2
    sselpwd
    @1
    @2
    @15
    @4
    @1
    cJ
    ctop
    wcel
    @15
    vy
    vz
    cA
    cJ
    cX
    crefi.x
    iscref
    simprbi
    3ad2ant1
    @1
    @2
    @4
    simp3
    @14
    @4
    @17
    wi
    vy
    cC
    @6
    @7
    cC
    wceq
    #
    @9
    @4
    @13
    @17
    @18
    @8
    @3
    cX
    @7
    cC
    unieq
    eqeq2d
    @18
    @11
    @16
    vz
    @12
    @7
    cC
    @10
    cref
    breq2
    rexbidv
    imbi12d
    rspcv
    syl3c
end
