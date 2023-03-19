include "wel.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "cfil.mm"
include "cfv.mm"
include "cufil.mm"
include "cdm.mm"
include "df-ufil.mm"
include "wceq.mm"
include "wa.mm"
include "pweq.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "difeq1.mm"
include "eleq12.mm"
include "sylan.mm"
include "orbi12d.mm"
include "raleqbidv.mm"
include "fveq2.mm"
include "fvex.mm"
include "elfvdm.mm"
include "elmptrab2.mm"

theorem isufil
  let vx: setvar x
  let cF: class F
  let cX: class X
  let vy: setvar y
  let vz: setvar z

  disjoint F x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X y
  disjoint X z
  assert |- ( F e. ( UFil ` X ) <-> ( F e. ( Fil ` X ) /\ A. x e. ~P X ( x e. F \/ ( X \ x ) e. F ) ) )

  proof
    vx
    vz
    wel
    #
    vy
    cv
    #
    vx
    cv
    #
    cdif
    #
    vz
    cv
    #
    wcel
    #
    wo
    #
    vx
    @1
    cpw
    #
    wral
    @2
    cF
    wcel
    #
    cX
    @2
    cdif
    #
    cF
    wcel
    #
    wo
    #
    vx
    cX
    cpw
    #
    wral
    vy
    vz
    @1
    cfil
    cfv
    cX
    cfil
    cfv
    cufil
    cfil
    cdm
    cX
    cF
    vx
    vz
    vy
    df-ufil
    @1
    cX
    wceq
    #
    @4
    cF
    wceq
    #
    wa
    #
    @6
    @11
    vx
    @7
    @12
    @13
    @7
    @12
    wceq
    @14
    @1
    cX
    pweq
    adantr
    @15
    @0
    @8
    @5
    @10
    @14
    @0
    @8
    wb
    @13
    @4
    cF
    @2
    eleq2
    adantl
    @13
    @3
    @9
    wceq
    @14
    @5
    @10
    wb
    @1
    cX
    @2
    difeq1
    @3
    @9
    @4
    cF
    eleq12
    sylan
    orbi12d
    raleqbidv
    @1
    cX
    cfil
    fveq2
    @1
    cfil
    fvex
    cF
    cX
    cfil
    elfvdm
    elmptrab2
end
