include "wf1o.mm"
include "cv.mm"
include "cid.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wiso.mm"
include "wcel.mm"
include "wceq.mm"
include "weq.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "sylan.mm"
include "fvex.mm"
include "ideq.mm"
include "a1i.mm"
include "ideqg.mm"
include "ad2antll.mm"
include "3bitr4rd.mm"
include "ralrimivva.mm"
include "pm4.71i.mm"
include "df-isom.mm"
include "bitr4i.mm"

theorem isof1oidb
  let cA: class A
  let cB: class B
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( H : A -1-1-onto-> B <-> H Isom _I , _I ( A , B ) )

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
    cid
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
    cid
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
    cid
    cid
    cH
    wiso
    @0
    @8
    @0
    @7
    vx
    vy
    cA
    cA
    @0
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    #
    wa
    #
    @4
    @5
    wceq
    #
    vx
    vy
    weq
    #
    @6
    @3
    @0
    cA
    cB
    cH
    wf1
    @11
    @13
    @14
    wb
    cA
    cB
    cH
    f1of1
    cA
    cB
    @1
    @2
    cH
    f1fveq
    sylan
    @6
    @13
    wb
    @12
    @4
    @5
    @2
    cH
    fvex
    ideq
    a1i
    @10
    @3
    @14
    wb
    @0
    @9
    @1
    @2
    cA
    ideqg
    ad2antll
    3bitr4rd
    ralrimivva
    pm4.71i
    vx
    vy
    cA
    cB
    cid
    cid
    cH
    df-isom
    bitr4i
end
