include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrinfmss.mm"
include "infcl.mm"

theorem infxrcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ RR* -> inf ( A , RR* , < ) e. RR* )

  proof
    cA
    cxr
    wss
    #
    vx
    vy
    vz
    cxr
    cA
    clt
    cxr
    clt
    wor
    @0
    xrltso
    a1i
    vx
    vy
    vz
    cA
    xrinfmss
    infcl
end
