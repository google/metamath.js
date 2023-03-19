include "ccolin.mm"
include "wrel.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "coprab.mm"
include "ccnv.mm"
include "relcnv.mm"
include "df-colinear.mm"
include "releqi.mm"
include "mpbir.mm"

theorem colinrel
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vn: setvar n


  assert |- Rel Colinear

  proof
    ccolin
    wrel
    vp
    cv
    #
    vn
    cv
    cee
    cfv
    #
    wcel
    vq
    cv
    #
    @1
    wcel
    vr
    cv
    #
    @1
    wcel
    w3a
    @0
    @2
    @3
    cop
    cbtwn
    wbr
    @2
    @3
    @0
    cop
    cbtwn
    wbr
    @3
    @0
    @2
    cop
    cbtwn
    wbr
    w3o
    wa
    vn
    cn
    wrex
    vq
    vr
    vp
    coprab
    #
    ccnv
    #
    wrel
    @4
    relcnv
    ccolin
    @5
    vn
    vp
    vq
    vr
    df-colinear
    releqi
    mpbir
end
