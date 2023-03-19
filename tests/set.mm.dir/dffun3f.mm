include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wex.mm"
include "dffun6f.mm"
include "nfcv.mm"
include "nfbr.mm"
include "mo2.mm"
include "albii.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dffun3f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vk: setvar k
  assume dffun3f.1: |- F/_ x A
  assume dffun3f.2: |- F/_ y A
  assume dffun3f.3: |- F/_ z A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k x
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
    vy
    wmo
    #
    vx
    wal
    #
    wa
    @0
    @3
    vy
    vz
    weq
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
    cA
    dffun3f.1
    dffun3f.2
    dffun6f
    @5
    @7
    @0
    @4
    @6
    vx
    @3
    vy
    vz
    vz
    @1
    @2
    cA
    vz
    @1
    nfcv
    dffun3f.3
    vz
    @2
    nfcv
    nfbr
    mo2
    albii
    anbi2i
    bitri
end
