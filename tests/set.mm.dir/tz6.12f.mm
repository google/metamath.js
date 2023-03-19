include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "weu.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "wb.mm"
include "nfel2.mm"
include "nfv.mm"
include "cbveu.mm"
include "a1i.mm"
include "anbi12d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "tz6.12.mm"
include "chvarv.mm"

theorem tz6.12f
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vz: setvar z
  assume tz6.12f.1: |- F/_ y F

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint F z
  assert |- ( ( <. A , y >. e. F /\ E! y <. A , y >. e. F ) -> ( F ` A ) = y )

  proof
    cA
    vz
    cv
    #
    cop
    #
    cF
    wcel
    #
    @2
    vz
    weu
    #
    wa
    #
    cA
    cF
    cfv
    #
    @0
    wceq
    #
    wi
    cA
    vy
    cv
    #
    cop
    #
    cF
    wcel
    #
    @9
    vy
    weu
    #
    wa
    #
    @5
    @7
    wceq
    #
    wi
    vz
    vy
    @0
    @7
    wceq
    #
    @4
    @11
    @6
    @12
    @13
    @2
    @9
    @3
    @10
    @13
    @1
    @8
    cF
    @0
    @7
    cA
    opeq2
    eleq1d
    #
    @3
    @10
    wb
    @13
    @2
    @9
    vz
    vy
    vy
    @1
    cF
    tz6.12f.1
    nfel2
    @9
    vz
    nfv
    @14
    cbveu
    a1i
    anbi12d
    @0
    @7
    @5
    eqeq2
    imbi12d
    vz
    cA
    cF
    tz6.12
    chvarv
end
