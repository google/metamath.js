include "weq.mm"
include "equequ1.mm"
include "equcom.mm"
include "3bitr3g.mm"

theorem equequ2OLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> ( z = x <-> z = y ) )

  proof
    vx
    vy
    weq
    vx
    vz
    weq
    vy
    vz
    weq
    vz
    vx
    weq
    vz
    vy
    weq
    vx
    vy
    vz
    equequ1
    vx
    vz
    equcom
    vy
    vz
    equcom
    3bitr3g
end
