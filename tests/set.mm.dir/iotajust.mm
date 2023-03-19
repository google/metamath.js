include "cab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "cbvabv.mm"
include "eqtri.mm"
include "unieqi.mm"

theorem iotajust
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint ph z
  disjoint ph y
  disjoint x y
  disjoint w x
  disjoint w z
  disjoint ph w
  disjoint w y
  assert |- U. { y | { x | ph } = { y } } = U. { z | { x | ph } = { z } }

  proof
    wph
    vx
    cab
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    cab
    #
    @0
    vz
    cv
    #
    csn
    #
    wceq
    #
    vz
    cab
    #
    @4
    @0
    vw
    cv
    #
    csn
    #
    wceq
    #
    vw
    cab
    @8
    @3
    @11
    vy
    vw
    @1
    @9
    wceq
    @2
    @10
    @0
    @1
    @9
    sneq
    eqeq2d
    cbvabv
    @11
    @7
    vw
    vz
    @9
    @5
    wceq
    @10
    @6
    @0
    @9
    @5
    sneq
    eqeq2d
    cbvabv
    eqtri
    unieqi
end
