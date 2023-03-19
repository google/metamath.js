include "wtr.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "dftr2.mm"
include "wceq.mm"
include "eleq12.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "anbi12d.mm"
include "adantr.mm"
include "imbi12d.mm"
include "spc2gv.mm"
include "pm2.43b.mm"
include "sylbi.mm"

theorem trel
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( Tr A -> ( ( B e. C /\ C e. A ) -> B e. A ) )

  proof
    cA
    wtr
    vy
    cv
    #
    vx
    cv
    #
    wcel
    #
    @1
    cA
    wcel
    #
    wa
    #
    @0
    cA
    wcel
    #
    wi
    #
    vx
    wal
    vy
    wal
    #
    cB
    cC
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    #
    cB
    cA
    wcel
    #
    wi
    #
    vy
    vx
    cA
    dftr2
    @7
    @10
    @11
    @6
    @12
    vy
    vx
    cB
    cC
    cC
    cA
    @0
    cB
    wceq
    #
    @1
    cC
    wceq
    #
    wa
    #
    @4
    @10
    @5
    @11
    @15
    @2
    @8
    @3
    @9
    @0
    cB
    @1
    cC
    eleq12
    @14
    @3
    @9
    wb
    @13
    @1
    cC
    cA
    eleq1
    adantl
    anbi12d
    @13
    @5
    @11
    wb
    @14
    @0
    cB
    cA
    eleq1
    adantr
    imbi12d
    spc2gv
    pm2.43b
    sylbi
end
