include "wcel.mm"
include "cop.mm"
include "c1st.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "opeq1.mm"
include "breq1d.mm"
include "eqeq2.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "opeq2.mm"
include "bibi1d.mm"
include "weq.mm"
include "breq2.mm"
include "eqeq1.mm"
include "vex.mm"
include "br1steq.mm"
include "vtoclbg.mm"
include "vtocl2g.mm"
include "3impia.mm"

theorem br1steqgOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( <. A , B >. 1st C <-> C = A ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    cC
    cX
    wcel
    #
    cA
    cB
    cop
    #
    cC
    c1st
    wbr
    #
    cC
    cA
    wceq
    #
    wb
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cC
    c1st
    wbr
    #
    cC
    @5
    wceq
    #
    wb
    #
    wi
    @0
    cA
    @6
    cop
    #
    cC
    c1st
    wbr
    #
    @3
    wb
    #
    wi
    @0
    @4
    wi
    vx
    vy
    cA
    cB
    cV
    cW
    @5
    cA
    wceq
    #
    @10
    @13
    @0
    @14
    @8
    @12
    @9
    @3
    @14
    @7
    @11
    cC
    c1st
    @5
    cA
    @6
    opeq1
    breq1d
    @5
    cA
    cC
    eqeq2
    bibi12d
    imbi2d
    @6
    cB
    wceq
    #
    @13
    @4
    @0
    @15
    @12
    @2
    @3
    @15
    @11
    @1
    cC
    c1st
    @6
    cB
    cA
    opeq2
    breq1d
    bibi1d
    imbi2d
    @7
    vz
    cv
    #
    c1st
    wbr
    vz
    vx
    weq
    @8
    @9
    vz
    cC
    cX
    @16
    cC
    @7
    c1st
    breq2
    @16
    cC
    @5
    eqeq1
    @5
    @6
    @16
    vx
    vex
    vy
    vex
    br1steq
    vtoclbg
    vtocl2g
    3impia
end
