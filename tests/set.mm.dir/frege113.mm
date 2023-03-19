include "wceq.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wi.mm"
include "wn.mm"
include "frege112.mm"
include "frege7.mm"
include "ax-mp.mm"

theorem frege113
  let cR: class R
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume frege112.z: |- Z e. V


  assert |- ( ( Z ( ( t+ ` R ) u. _I ) X -> ( -. Z ( t+ ` R ) X -> Z = X ) ) -> ( Z ( ( t+ ` R ) u. _I ) X -> ( -. Z ( t+ ` R ) X -> X ( ( t+ ` R ) u. _I ) Z ) ) )

  proof
    cZ
    cX
    wceq
    #
    cX
    cZ
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
    wbr
    #
    wi
    cZ
    cX
    @2
    wbr
    #
    cZ
    cX
    @1
    wbr
    wn
    #
    @0
    wi
    wi
    @4
    @5
    @3
    wi
    wi
    wi
    cR
    cV
    cX
    cZ
    frege112.z
    frege112
    @0
    @3
    @4
    @5
    frege7
    ax-mp
end
