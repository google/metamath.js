include "c0v.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "cpjh.mm"
include "wceq.mm"
include "csh.mm"
include "chshii.mm"
include "oc0.mm"
include "ax-mp.mm"
include "ax-hv0cl.mm"
include "pjoc2i.mm"
include "mpbi.mm"

theorem pj0i
  let cH: class H
  assume pj0.1: |- H e. CH


  assert |- ( ( projh ` H ) ` 0h ) = 0h

  proof
    c0v
    cH
    cort
    cfv
    wcel
    #
    c0v
    cH
    cpjh
    cfv
    cfv
    c0v
    wceq
    cH
    csh
    wcel
    @0
    cH
    pj0.1
    chshii
    cH
    oc0
    ax-mp
    c0v
    cH
    pj0.1
    ax-hv0cl
    pjoc2i
    mpbi
end
