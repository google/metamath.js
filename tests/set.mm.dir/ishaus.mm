include "cv.mm"
include "wne.mm"
include "wel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "cuni.mm"
include "wral.mm"
include "ctop.mm"
include "cha.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "rexeq.mm"
include "rexeqbi1dv.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "df-haus.mm"
include "elrab2.mm"

theorem ishaus
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vj: setvar j
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J

  disjoint x y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint J m
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B o
  disjoint B x
  disjoint B z
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m o
  disjoint m z
  disjoint n o
  disjoint n z
  disjoint J o
  disjoint J z
  disjoint X j
  disjoint X o
  disjoint X z
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint Q m
  disjoint Q n
  disjoint Q y
  assert |- ( J e. Haus <-> ( J e. Top /\ A. x e. X A. y e. X ( x =/= y -> E. n e. J E. m e. J ( x e. n /\ y e. m /\ ( n i^i m ) = (/) ) ) ) )

  proof
    vx
    cv
    vy
    cv
    wne
    #
    vx
    vn
    wel
    vy
    vm
    wel
    vn
    cv
    vm
    cv
    cin
    c0
    wceq
    w3a
    #
    vm
    vj
    cv
    #
    wrex
    #
    vn
    @2
    wrex
    #
    wi
    #
    vy
    @2
    cuni
    #
    wral
    #
    vx
    @6
    wral
    @0
    @1
    vm
    cJ
    wrex
    #
    vn
    cJ
    wrex
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    vj
    cJ
    ctop
    cha
    @2
    cJ
    wceq
    #
    @7
    @11
    vx
    @6
    cX
    @12
    @6
    cJ
    cuni
    cX
    @2
    cJ
    unieq
    ist0.1
    syl6eqr
    #
    @12
    @5
    @10
    vy
    @6
    cX
    @13
    @12
    @4
    @9
    @0
    @3
    @8
    vn
    @2
    cJ
    @1
    vm
    @2
    cJ
    rexeq
    rexeqbi1dv
    imbi2d
    raleqbidv
    raleqbidv
    vx
    vy
    vj
    vm
    vn
    df-haus
    elrab2
end
