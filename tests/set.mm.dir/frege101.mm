include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "frege100.mm"
include "frege48.mm"
include "ax-mp.mm"

theorem frege101
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume frege99.z: |- Z e. U


  assert |- ( ( Z = X -> ( Z R V -> X ( t+ ` R ) V ) ) -> ( ( X ( t+ ` R ) Z -> ( Z R V -> X ( t+ ` R ) V ) ) -> ( X ( ( t+ ` R ) u. _I ) Z -> ( Z R V -> X ( t+ ` R ) V ) ) ) )

  proof
    cX
    cZ
    cR
    ctcl
    cfv
    #
    cid
    cun
    wbr
    #
    cX
    cZ
    @0
    wbr
    #
    wn
    cZ
    cX
    wceq
    #
    wi
    wi
    @3
    cZ
    cV
    cR
    wbr
    cX
    cV
    @0
    wbr
    wi
    #
    wi
    @2
    @4
    wi
    @1
    @4
    wi
    wi
    wi
    cR
    cU
    cX
    cZ
    frege99.z
    frege100
    @1
    @2
    @3
    @4
    frege48
    ax-mp
end
