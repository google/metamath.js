include "cint.mm"
include "wel.mm"
include "wral.mm"
include "cab.mm"
include "dfint2.mm"
include "nfv.mm"
include "nfral.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfint
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume nfint.1: |- F/_ x A


  assert |- F/_ x |^| A

  proof
    vx
    cA
    cint
    vy
    vz
    wel
    #
    vz
    cA
    wral
    #
    vy
    cab
    vy
    vz
    cA
    dfint2
    @1
    vx
    vy
    @0
    vx
    vz
    cA
    nfint.1
    @0
    vx
    nfv
    nfral
    nfab
    nfcxfr
end
