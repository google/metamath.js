include "cc.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "casin.mm"
include "cfv.mm"
include "cmin.mm"
include "cacos.mm"
include "df-acos.mm"
include "wcel.mm"
include "picn.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "asincl.mm"
include "subcl.mm"
include "sylancr.mm"
include "fmpti.mm"

theorem acosf
  let vx: setvar x


  assert |- arccos : CC --> CC

  proof
    vx
    cc
    cc
    cpi
    c2
    cdiv
    co
    #
    vx
    cv
    #
    casin
    cfv
    #
    cmin
    co
    #
    cacos
    vx
    df-acos
    @1
    cc
    wcel
    @0
    cc
    wcel
    #
    @2
    cc
    wcel
    @3
    cc
    wcel
    cpi
    cc
    wcel
    @4
    picn
    cpi
    halfcl
    ax-mp
    @1
    asincl
    @0
    @2
    subcl
    sylancr
    fmpti
end
