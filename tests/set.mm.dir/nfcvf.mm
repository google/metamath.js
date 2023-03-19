include "cv.mm"
include "nfcv.mm"
include "weq.mm"
include "id.mm"
include "dvelimc.mm"

theorem nfcvf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. x x = y -> F/_ x y )

  proof
    vx
    vy
    vz
    vz
    cv
    #
    vy
    cv
    #
    vx
    @0
    nfcv
    vz
    @1
    nfcv
    vz
    vy
    weq
    id
    dvelimc
end
