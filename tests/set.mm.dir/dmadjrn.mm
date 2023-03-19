include "cado.mm"
include "cdm.mm"
include "wf1o.mm"
include "wf.mm"
include "adj1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"

theorem dmadjrn
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. dom adjh -> ( adjh ` T ) e. dom adjh )

  proof
    cado
    cdm
    #
    @0
    cT
    cado
    @0
    @0
    cado
    wf1o
    @0
    @0
    cado
    wf
    adj1o
    @0
    @0
    cado
    f1of
    ax-mp
    ffvelrni
end
