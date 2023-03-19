include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "dffun2.mm"
include "wmo.mm"
include "breq2.mm"
include "mo4.mm"
include "mo2v.mm"
include "bitr3i.mm"
include "albii.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dffun3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( Fun A <-> ( Rel A /\ A. x E. z A. y ( x A y -> y = z ) ) )

  proof
    cA
    wfun
    cA
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    @1
    vz
    cv
    #
    cA
    wbr
    #
    wa
    vy
    vz
    weq
    #
    wi
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    wa
    @0
    @3
    @6
    wi
    vy
    wal
    vz
    wex
    #
    vx
    wal
    #
    wa
    vx
    vy
    vz
    cA
    dffun2
    @8
    @10
    @0
    @7
    @9
    vx
    @7
    @3
    vy
    wmo
    @9
    @3
    @5
    vy
    vz
    @2
    @4
    @1
    cA
    breq2
    mo4
    @3
    vy
    vz
    mo2v
    bitr3i
    albii
    anbi2i
    bitri
end
