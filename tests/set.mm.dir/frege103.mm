include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "frege100.mm"
include "frege19.mm"
include "ax-mp.mm"

theorem frege103
  let cR: class R
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume frege103.z: |- Z e. V


  assert |- ( ( Z = X -> X = Z ) -> ( X ( ( t+ ` R ) u. _I ) Z -> ( -. X ( t+ ` R ) Z -> X = Z ) ) )

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
    wn
    #
    cZ
    cX
    wceq
    #
    wi
    wi
    @3
    cX
    cZ
    wceq
    #
    wi
    @1
    @2
    @4
    wi
    wi
    wi
    cR
    cV
    cX
    cZ
    frege103.z
    frege100
    @1
    @2
    @3
    @4
    frege19
    ax-mp
end
