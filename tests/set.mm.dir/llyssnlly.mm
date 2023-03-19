include "clly.mm"
include "cnlly.mm"
include "cv.mm"
include "llynlly.mm"
include "ssriv.mm"

theorem llyssnlly
  let cA: class A
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cP: class P
  let cU: class U
  let cJ: class J
  let cV: class V


  assert |- Locally A C_ N-Locally A

  proof
    vj
    cA
    clly
    cA
    cnlly
    cA
    vj
    cv
    llynlly
    ssriv
end
