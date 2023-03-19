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
include "frege52aid.mm"
include "ax-mp.mm"

theorem frege105
  let cR: class R
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume frege103.z: |- Z e. V


  assert |- ( ( -. X ( t+ ` R ) Z -> Z = X ) -> X ( ( t+ ` R ) u. _I ) Z )

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
    @1
    @2
    wi
    cR
    cV
    cX
    cZ
    frege103.z
    dffrege99
    @1
    @2
    frege52aid
    ax-mp
end
