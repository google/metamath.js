include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "ccnv.mm"
include "wiso.mm"
include "ralcom.mm"
include "vex.mm"
include "brcnv.mm"
include "fvex.mm"
include "bibi12i.mm"
include "2ralbii.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "df-isom.mm"
include "3bitr4i.mm"

theorem isocnv2
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( H Isom R , S ( A , B ) <-> H Isom `' R , `' S ( A , B ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    @1
    cH
    cfv
    #
    @2
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vx
    cA
    wral
    vy
    cA
    wral
    #
    wa
    @0
    @2
    @1
    cR
    ccnv
    #
    wbr
    #
    @5
    @4
    cS
    ccnv
    #
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cB
    @9
    @11
    cH
    wiso
    @8
    @14
    @0
    @8
    @7
    vy
    cA
    wral
    vx
    cA
    wral
    @14
    @7
    vy
    vx
    cA
    cA
    ralcom
    @13
    @7
    vx
    vy
    cA
    cA
    @10
    @3
    @12
    @6
    @2
    @1
    cR
    vx
    vex
    vy
    vex
    brcnv
    @5
    @4
    cS
    @2
    cH
    fvex
    @1
    cH
    fvex
    brcnv
    bibi12i
    2ralbii
    bitr4i
    anbi2i
    vy
    vx
    cA
    cB
    cR
    cS
    cH
    df-isom
    vx
    vy
    cA
    cB
    @9
    @11
    cH
    df-isom
    3bitr4i
end
