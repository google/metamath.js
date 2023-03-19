include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "cid.mm"
include "cun.mm"
include "wb.mm"
include "dffrege99.mm"
include "frege57aid.mm"
include "ax-mp.mm"

theorem frege100
  let cR: class R
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume frege99.z: |- Z e. U


  assert |- ( X ( ( t+ ` R ) u. _I ) Z -> ( -. X ( t+ ` R ) Z -> Z = X ) )

  proof
    cX
    cZ
    cR
    ctcl
    cfv
    #
    wbr
    wn
    cZ
    cX
    wceq
    wi
    #
    cX
    cZ
    @0
    cid
    cun
    wbr
    #
    wb
    @2
    @1
    wi
    cR
    cU
    cX
    cZ
    frege99.z
    dffrege99
    @1
    @2
    frege57aid
    ax-mp
end
