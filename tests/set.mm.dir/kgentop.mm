include "ckgen.mm"
include "crn.mm"
include "ctop.mm"
include "wf.mm"
include "wss.mm"
include "kgenf.mm"
include "frn.mm"
include "ax-mp.mm"
include "sseli.mm"

theorem kgentop
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cK: class K


  assert |- ( J e. ran kGen -> J e. Top )

  proof
    ckgen
    crn
    #
    ctop
    cJ
    ctop
    ctop
    ckgen
    wf
    @0
    ctop
    wss
    kgenf
    ctop
    ctop
    ckgen
    frn
    ax-mp
    sseli
end
