include "cina.mm"
include "wcel.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "ccf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "elex.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "3ad2ant2.mm"
include "neeq1.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq12.mm"
include "mpancom.mm"
include "breq2.mm"
include "raleqbi1dv.mm"
include "3anbi123d.mm"
include "df-ina.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elina
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A e. Inacc <-> ( A =/= (/) /\ ( cf ` A ) = A /\ A. x e. A ~P x ~< A ) )

  proof
    cA
    cina
    wcel
    cA
    cvv
    wcel
    #
    cA
    c0
    wne
    #
    cA
    ccf
    cfv
    #
    cA
    wceq
    #
    vx
    cv
    cpw
    #
    cA
    csdm
    wbr
    #
    vx
    cA
    wral
    #
    w3a
    #
    cA
    cina
    elex
    @3
    @1
    @0
    @6
    @3
    @2
    cvv
    wcel
    @0
    cA
    ccf
    fvex
    @2
    cA
    cvv
    eleq1
    mpbii
    3ad2ant2
    vy
    cv
    #
    c0
    wne
    #
    @8
    ccf
    cfv
    #
    @8
    wceq
    #
    @4
    @8
    csdm
    wbr
    #
    vx
    @8
    wral
    #
    w3a
    @7
    vy
    cA
    cina
    cvv
    @8
    cA
    wceq
    #
    @9
    @1
    @11
    @3
    @13
    @6
    @8
    cA
    c0
    neeq1
    @10
    @2
    wceq
    @14
    @11
    @3
    wb
    @8
    cA
    ccf
    fveq2
    @10
    @2
    @8
    cA
    eqeq12
    mpancom
    @12
    @5
    vx
    @8
    cA
    @8
    cA
    @4
    csdm
    breq2
    raleqbi1dv
    3anbi123d
    vy
    vx
    df-ina
    elab2g
    pm5.21nii
end
