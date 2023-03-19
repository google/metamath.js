include "weq.mm"
include "nfv.mm"
include "equequ1.mm"
include "sbie.mm"

theorem equsb3lem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint y z
  disjoint x y
  assert |- ( [ x / y ] y = z <-> x = z )

  proof
    vy
    vz
    weq
    vx
    vz
    weq
    #
    vy
    vx
    @0
    vy
    nfv
    vy
    vx
    vz
    equequ1
    sbie
end
