include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "wa.mm"
include "dfss2.mm"
include "id.mm"
include "simpr.mm"
include "syl.mm"
include "simpl.mm"
include "idd.mm"
include "ssel2.mm"
include "syl6an.mm"
include "idiALT.mm"
include "alrimiv.mm"
include "biimpr.mm"
include "mpsyl.mm"

theorem sstrALT2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A C_ B /\ B C_ C ) -> A C_ C )

  proof
    cA
    cC
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    @1
    cC
    wcel
    #
    wi
    #
    vx
    wal
    #
    wb
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
    @5
    @0
    vx
    cA
    cC
    dfss2
    @8
    @4
    vx
    @8
    @4
    wi
    @8
    @7
    @2
    @1
    cB
    wcel
    #
    @3
    @8
    @8
    @7
    @8
    id
    #
    @6
    @7
    simpr
    syl
    @8
    @6
    @2
    @2
    @9
    @8
    @8
    @6
    @10
    @6
    @7
    simpl
    syl
    @8
    @2
    idd
    cA
    cB
    @1
    ssel2
    syl6an
    cB
    cC
    @1
    ssel2
    syl6an
    idiALT
    alrimiv
    @0
    @5
    biimpr
    mpsyl
end
