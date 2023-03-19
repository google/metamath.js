include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "dfss2.mm"
include "idn1.mm"
include "simpr.mm"
include "e1a.mm"
include "simpl.mm"
include "idn2.mm"
include "ssel2.mm"
include "e12an.mm"
include "in2.mm"
include "gen11.mm"
include "biimpr.mm"
include "e01.mm"
include "in1.mm"

theorem sstrALT2VD
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A C_ B /\ B C_ C ) -> A C_ C )

  proof
    cA
    cB
    wss
    #
    cB
    cC
    wss
    #
    wa
    #
    cA
    cC
    wss
    #
    @3
    vx
    cv
    #
    cA
    wcel
    #
    @4
    cC
    wcel
    #
    wi
    #
    vx
    wal
    #
    wb
    @2
    @8
    @3
    vx
    cA
    cC
    dfss2
    @2
    @7
    vx
    @2
    @5
    @6
    @2
    @1
    @5
    @4
    cB
    wcel
    #
    @6
    @2
    @2
    @1
    @2
    idn1
    #
    @0
    @1
    simpr
    e1a
    @2
    @0
    @5
    @5
    @9
    @2
    @2
    @0
    @10
    @0
    @1
    simpl
    e1a
    @2
    @5
    idn2
    cA
    cB
    @4
    ssel2
    e12an
    cB
    cC
    @4
    ssel2
    e12an
    in2
    gen11
    @3
    @8
    biimpr
    e01
    in1
end
