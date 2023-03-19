include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "frege104.mm"
include "frege113.mm"
include "ax-mp.mm"

theorem frege114
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume frege114.x: |- X e. U
  assume frege114.z: |- Z e. V


  assert |- ( Z ( ( t+ ` R ) u. _I ) X -> ( -. Z ( t+ ` R ) X -> X ( ( t+ ` R ) u. _I ) Z ) )

  proof
    cZ
    cX
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
    wbr
    #
    cZ
    cX
    @0
    wbr
    wn
    #
    cZ
    cX
    wceq
    wi
    wi
    @2
    @3
    cX
    cZ
    @1
    wbr
    wi
    wi
    cR
    cU
    cZ
    cX
    frege114.x
    frege104
    cR
    cV
    cX
    cZ
    frege114.z
    frege113
    ax-mp
end
