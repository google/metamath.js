include "csconn.mm"
include "wcel.mm"
include "cpconn.mm"
include "ctop.mm"
include "sconnpconn.mm"
include "pconntop.mm"
include "syl.mm"

theorem sconntop
  let cJ: class J
  let cF: class F
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y


  assert |- ( J e. SConn -> J e. Top )

  proof
    cJ
    csconn
    wcel
    cJ
    cpconn
    wcel
    cJ
    ctop
    wcel
    cJ
    sconnpconn
    cJ
    pconntop
    syl
end
