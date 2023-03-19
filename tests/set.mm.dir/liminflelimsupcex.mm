include "c0.mm"
include "clsp.mm"
include "cfv.mm"
include "clsi.mm"
include "clt.mm"
include "wbr.mm"
include "cmnf.mm"
include "cpnf.mm"
include "mnfltpnf.mm"
include "limsup0.mm"
include "liminf0.mm"
include "breq12i.mm"
include "mpbir.mm"

theorem liminflelimsupcex
  let vk: setvar k
  let vx: setvar x


  assert |- ( limsup ` (/) ) < ( liminf ` (/) )

  proof
    c0
    clsp
    cfv
    #
    c0
    clsi
    cfv
    #
    clt
    wbr
    cmnf
    cpnf
    clt
    wbr
    mnfltpnf
    @0
    cmnf
    @1
    cpnf
    clt
    limsup0
    liminf0
    breq12i
    mpbir
end
