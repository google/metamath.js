include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "wdisj.mm"
include "nfcri.mm"
include "weq.mm"
include "eleq2d.mm"
include "cbvrmo.mm"
include "albii.mm"
include "df-disj.mm"
include "3bitr4i.mm"

theorem cbvdisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  assume cbvdisj.1: |- F/_ y B
  assume cbvdisj.2: |- F/_ x C
  assume cbvdisj.3: |- ( x = y -> B = C )

  disjoint x y
  disjoint A x
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
    @1
    @3
    vx
    vy
    cA
    vy
    vz
    cB
    cbvdisj.1
    nfcri
    vx
    vz
    cC
    cbvdisj.2
    nfcri
    vx
    vy
    weq
    cB
    cC
    @0
    cbvdisj.3
    eleq2d
    cbvrmo
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
