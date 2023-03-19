include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "cid.mm"
include "cun.mm"
include "frege105.mm"
include "frege37.mm"
include "ax-mp.mm"

theorem frege106
  let cR: class R
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume frege103.z: |- Z e. V


  assert |- ( X ( t+ ` R ) Z -> X ( ( t+ ` R ) u. _I ) Z )

  proof
    cX
    cZ
    cR
    ctcl
    cfv
    #
    wbr
    #
    wn
    cZ
    cX
    wceq
    #
    wi
    cX
    cZ
    @0
    cid
    cun
    wbr
    #
    wi
    @1
    @3
    wi
    cR
    cV
    cX
    cZ
    frege103.z
    frege105
    @1
    @2
    @3
    frege37
    ax-mp
end
