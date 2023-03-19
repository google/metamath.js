include "wceq.mm"
include "wi.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "elexi.mm"
include "eqeq1.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "frege55c.mm"
include "vtocl.mm"
include "frege103.mm"
include "ax-mp.mm"

theorem frege104
  let cR: class R
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vz: setvar z
  assume frege103.z: |- Z e. V


  assert |- ( X ( ( t+ ` R ) u. _I ) Z -> ( -. X ( t+ ` R ) Z -> X = Z ) )

  proof
    cZ
    cX
    wceq
    #
    cX
    cZ
    wceq
    #
    wi
    #
    cX
    cZ
    cR
    ctcl
    cfv
    #
    cid
    cun
    wbr
    cX
    cZ
    @3
    wbr
    wn
    @1
    wi
    wi
    vz
    cv
    #
    cX
    wceq
    #
    cX
    @4
    wceq
    #
    wi
    @2
    vz
    cZ
    cZ
    cV
    frege103.z
    elexi
    @4
    cZ
    wceq
    @5
    @0
    @6
    @1
    @4
    cZ
    cX
    eqeq1
    @4
    cZ
    cX
    eqeq2
    imbi12d
    vz
    cX
    frege55c
    vtocl
    cR
    cV
    cX
    cZ
    frege103.z
    frege103
    ax-mp
end
