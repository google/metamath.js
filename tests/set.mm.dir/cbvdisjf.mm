include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "wdisj.mm"
include "wa.mm"
include "wmo.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "cbvmo.mm"
include "df-rmo.mm"
include "3bitr4i.mm"
include "albii.mm"
include "df-disj.mm"

theorem cbvdisjf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  assume cbvdisjf.1: |- F/_ x A
  assume cbvdisjf.2: |- F/_ y B
  assume cbvdisjf.3: |- F/_ x C
  assume cbvdisjf.4: |- ( x = y -> B = C )

  disjoint x y
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  assert |- ( Disj_ x e. A B <-> Disj_ y e. A C )

  proof
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrmo
    #
    vz
    wal
    @0
    cC
    wcel
    #
    vy
    cA
    wrmo
    #
    vz
    wal
    vx
    cA
    cB
    wdisj
    vy
    cA
    cC
    wdisj
    @2
    @4
    vz
    vx
    cv
    #
    cA
    wcel
    #
    @1
    wa
    #
    vx
    wmo
    vy
    cv
    #
    cA
    wcel
    #
    @3
    wa
    #
    vy
    wmo
    @2
    @4
    @7
    @10
    vx
    vy
    @6
    @1
    vy
    @6
    vy
    nfv
    vy
    vz
    cB
    cbvdisjf.2
    nfcri
    nfan
    @9
    @3
    vx
    vx
    vy
    cA
    cbvdisjf.1
    nfcri
    vx
    vz
    cC
    cbvdisjf.3
    nfcri
    nfan
    vx
    vy
    weq
    #
    @6
    @9
    @1
    @3
    @5
    @8
    cA
    eleq1
    @11
    cB
    cC
    @0
    cbvdisjf.4
    eleq2d
    anbi12d
    cbvmo
    @1
    vx
    cA
    df-rmo
    @3
    vy
    cA
    df-rmo
    3bitr4i
    albii
    vx
    vz
    cA
    cB
    df-disj
    vy
    vz
    cA
    cC
    df-disj
    3bitr4i
end
