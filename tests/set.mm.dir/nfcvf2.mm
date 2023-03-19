include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "naecoms.mm"

theorem nfcvf2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. x x = y -> F/_ y x )

  proof
    vy
    vx
    cv
    wnfc
    vy
    vx
    vy
    vx
    nfcvf
    naecoms
end
