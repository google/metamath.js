include "ct0.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wi.mm"
include "t0sep.mm"
include "necon3ad.mm"
include "exp32.mm"
include "3imp2.mm"
include "rexnal.mm"
include "sylibr.mm"

theorem t0dist
  let cA: class A
  let cB: class B
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J

  disjoint A o
  disjoint B o
  disjoint J o
  disjoint X o
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
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
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X j
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint Q m
  disjoint Q n
  disjoint Q y
  assert |- ( ( J e. Kol2 /\ ( A e. X /\ B e. X /\ A =/= B ) ) -> E. o e. J -. ( A e. o <-> B e. o ) )

  proof
    cJ
    ct0
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    wa
    cA
    vo
    cv
    #
    wcel
    cB
    @4
    wcel
    wb
    #
    vo
    cJ
    wral
    #
    wn
    #
    @5
    wn
    vo
    cJ
    wrex
    @0
    @1
    @2
    @3
    @7
    @0
    @1
    @2
    @3
    @7
    wi
    @0
    @1
    @2
    wa
    wa
    @6
    cA
    cB
    vo
    cA
    cB
    cJ
    cX
    ist0.1
    t0sep
    necon3ad
    exp32
    3imp2
    @5
    vo
    cJ
    rexnal
    sylibr
end
