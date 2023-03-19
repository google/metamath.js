include "clly.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "islly.mm"
include "simplbi.mm"

theorem llytop
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


  assert |- ( J e. Locally A -> J e. Top )

  proof
    cJ
    cA
    clly
    wcel
    cJ
    ctop
    wcel
    vy
    cv
    vu
    cv
    #
    wcel
    cJ
    @0
    crest
    co
    cA
    wcel
    wa
    vu
    cJ
    vx
    cv
    #
    cpw
    cin
    wrex
    vy
    @1
    wral
    vx
    cJ
    wral
    vx
    vy
    vu
    cA
    cJ
    islly
    simplbi
end
