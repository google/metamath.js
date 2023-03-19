include "wf1o.mm"
include "cv.mm"
include "cvv.mm"
include "cxp.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wiso.mm"
include "wcel.mm"
include "cop.mm"
include "fvex.mm"
include "opelvv.mm"
include "df-br.mm"
include "mpbir.mm"
include "a1i.mm"
include "opelvvg.mm"
include "sylibr.mm"
include "a1d.mm"
include "impbid2.mm"
include "adantl.mm"
include "ralrimivva.mm"
include "pm4.71i.mm"
include "df-isom.mm"
include "bitr4i.mm"

theorem isof1oopb
  let cA: class A
  let cB: class B
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( H : A -1-1-onto-> B <-> H Isom ( _V X. _V ) , ( _V X. _V ) ( A , B ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cvv
    cvv
    cxp
    #
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
    @3
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
    @3
    @3
    cH
    wiso
    @0
    @9
    @0
    @8
    vx
    vy
    cA
    cA
    @1
    cA
    wcel
    @2
    cA
    wcel
    wa
    #
    @8
    @0
    @10
    @4
    @7
    @7
    @4
    @7
    @5
    @6
    cop
    @3
    wcel
    @5
    @6
    @1
    cH
    fvex
    @2
    cH
    fvex
    opelvv
    @5
    @6
    @3
    df-br
    mpbir
    a1i
    @10
    @4
    @7
    @10
    @1
    @2
    cop
    @3
    wcel
    @4
    @1
    @2
    cA
    cA
    opelvvg
    @1
    @2
    @3
    df-br
    sylibr
    a1d
    impbid2
    adantl
    ralrimivva
    pm4.71i
    vx
    vy
    cA
    cB
    @3
    @3
    cH
    df-isom
    bitr4i
end
