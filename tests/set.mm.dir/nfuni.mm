include "cuni.mm"
include "wel.mm"
include "wrex.mm"
include "cab.mm"
include "dfuni2.mm"
include "nfv.mm"
include "nfrex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfuni
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume nfuni.1: |- F/_ x A


  assert |- F/_ x U. A

  proof
    vx
    cA
    cuni
    vy
    vz
    wel
    #
    vz
    cA
    wrex
    #
    vy
    cab
    vy
    vz
    cA
    dfuni2
    @1
    vx
    vy
    @0
    vx
    vz
    cA
    nfuni.1
    @0
    vx
    nfv
    nfrex
    nfab
    nfcxfr
end
