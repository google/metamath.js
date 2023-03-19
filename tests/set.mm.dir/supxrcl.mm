include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrsupss.mm"
include "supcl.mm"

theorem supxrcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B


  assert |- ( A C_ RR* -> sup ( A , RR* , < ) e. RR* )

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
    xrsupss
    supcl
end
