include "cnlly.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "isnlly.mm"
include "simplbi.mm"

theorem nllytop
  let cA: class A
  let cJ: class J
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
  let cV: class V


  assert |- ( J e. N-Locally A -> J e. Top )

  proof
    cJ
    cA
    cnlly
    wcel
    cJ
    ctop
    wcel
    cJ
    vu
    cv
    crest
    co
    cA
    wcel
    vu
    vy
    cv
    csn
    cJ
    cnei
    cfv
    cfv
    vx
    cv
    #
    cpw
    cin
    wrex
    vy
    @0
    wral
    vx
    cJ
    wral
    vx
    vy
    vu
    cA
    cJ
    isnlly
    simplbi
end
