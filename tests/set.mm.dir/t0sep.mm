include "ct0.mm"
include "wcel.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "ctop.mm"
include "ist0.mm"
include "simprbi.mm"
include "eleq1.mm"
include "bibi1d.mm"
include "ralbidv.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "bibi2d.mm"
include "eqeq2.mm"
include "rspc2va.mm"
include "ancoms.mm"
include "sylan.mm"

theorem t0sep
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J

  disjoint A x
  disjoint B x
  disjoint J x
  disjoint X x
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B o
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
  disjoint J o
  disjoint J y
  disjoint J z
  disjoint X j
  disjoint X o
  disjoint X y
  disjoint X z
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint Q m
  disjoint Q n
  disjoint Q y
  assert |- ( ( J e. Kol2 /\ ( A e. X /\ B e. X ) ) -> ( A. x e. J ( A e. x <-> B e. x ) -> A = B ) )

  proof
    cJ
    ct0
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    wcel
    #
    vz
    cv
    #
    @2
    wcel
    #
    wb
    #
    vx
    cJ
    wral
    #
    @1
    @4
    wceq
    #
    wi
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    wa
    #
    cA
    @2
    wcel
    #
    cB
    @2
    wcel
    #
    wb
    #
    vx
    cJ
    wral
    #
    cA
    cB
    wceq
    #
    wi
    #
    @0
    cJ
    ctop
    wcel
    @10
    vy
    vz
    vx
    cJ
    cX
    ist0.1
    ist0
    simprbi
    @11
    @10
    @17
    @9
    @17
    @12
    @5
    wb
    #
    vx
    cJ
    wral
    #
    cA
    @4
    wceq
    #
    wi
    vy
    vz
    cA
    cB
    cX
    cX
    @1
    cA
    wceq
    #
    @7
    @19
    @8
    @20
    @21
    @6
    @18
    vx
    cJ
    @21
    @3
    @12
    @5
    @1
    cA
    @2
    eleq1
    bibi1d
    ralbidv
    @1
    cA
    @4
    eqeq1
    imbi12d
    @4
    cB
    wceq
    #
    @19
    @15
    @20
    @16
    @22
    @18
    @14
    vx
    cJ
    @22
    @5
    @13
    @12
    @4
    cB
    @2
    eleq1
    bibi2d
    ralbidv
    @4
    cB
    cA
    eqeq2
    imbi12d
    rspc2va
    ancoms
    sylan
end
