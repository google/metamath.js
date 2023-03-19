include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wcel.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "ctop.mm"
include "c1stc.mm"
include "wceq.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "pweq.mm"
include "raleq.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "raleqbidv.mm"
include "df-1stc.mm"
include "elrab2.mm"

theorem is1stc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cX: class X
  let vw: setvar w
  let vj: setvar j
  assume is1stc.1: |- X = U. J

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint X j
  assert |- ( J e. 1stc <-> ( J e. Top /\ A. x e. X E. y e. ~P J ( y ~<_ _om /\ A. z e. J ( x e. z -> x e. U. ( y i^i ~P z ) ) ) ) )

  proof
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vx
    cv
    #
    vz
    cv
    #
    wcel
    @2
    @0
    @3
    cpw
    cin
    cuni
    wcel
    wi
    #
    vz
    vj
    cv
    #
    wral
    #
    wa
    #
    vy
    @5
    cpw
    #
    wrex
    #
    vx
    @5
    cuni
    #
    wral
    @1
    @4
    vz
    cJ
    wral
    #
    wa
    #
    vy
    cJ
    cpw
    #
    wrex
    #
    vx
    cX
    wral
    vj
    cJ
    ctop
    c1stc
    @5
    cJ
    wceq
    #
    @9
    @14
    vx
    @10
    cX
    @15
    @10
    cJ
    cuni
    cX
    @5
    cJ
    unieq
    is1stc.1
    syl6eqr
    @15
    @7
    @12
    vy
    @8
    @13
    @5
    cJ
    pweq
    @15
    @6
    @11
    @1
    @4
    vz
    @5
    cJ
    raleq
    anbi2d
    rexeqbidv
    raleqbidv
    vx
    vy
    vz
    vj
    df-1stc
    elrab2
end
