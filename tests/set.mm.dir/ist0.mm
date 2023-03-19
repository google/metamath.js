include "wel.mm"
include "wb.mm"
include "cv.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "cuni.mm"
include "ctop.mm"
include "ct0.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "raleq.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "df-t0.mm"
include "elrab2.mm"

theorem ist0
  let vx: setvar x
  let vy: setvar y
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J

  disjoint o x
  disjoint o y
  disjoint x y
  disjoint J o
  disjoint J x
  disjoint J y
  disjoint X o
  disjoint X x
  disjoint X y
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
  disjoint m n
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint J z
  disjoint X j
  disjoint X z
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint Q m
  disjoint Q n
  disjoint Q y
  assert |- ( J e. Kol2 <-> ( J e. Top /\ A. x e. X A. y e. X ( A. o e. J ( x e. o <-> y e. o ) -> x = y ) ) )

  proof
    vx
    vo
    wel
    vy
    vo
    wel
    wb
    #
    vo
    vj
    cv
    #
    wral
    #
    vx
    cv
    vy
    cv
    wceq
    #
    wi
    #
    vy
    @1
    cuni
    #
    wral
    #
    vx
    @5
    wral
    @0
    vo
    cJ
    wral
    #
    @3
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
    ct0
    @1
    cJ
    wceq
    #
    @6
    @9
    vx
    @5
    cX
    @10
    @5
    cJ
    cuni
    cX
    @1
    cJ
    unieq
    ist0.1
    syl6eqr
    #
    @10
    @4
    @8
    vy
    @5
    cX
    @11
    @10
    @2
    @7
    @3
    @0
    vo
    @1
    cJ
    raleq
    imbi1d
    raleqbidv
    raleqbidv
    vx
    vy
    vj
    vo
    df-t0
    elrab2
end
