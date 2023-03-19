include "cc.mm"
include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "ccos.mm"
include "df-cos.mm"
include "wcel.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "efcl.mm"
include "syl.mm"
include "negicn.mm"
include "addcld.mm"
include "halfcld.mm"
include "fmpti.mm"

theorem cosf
  let vx: setvar x


  assert |- cos : CC --> CC

  proof
    vx
    cc
    cc
    ci
    vx
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @0
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    ccos
    vx
    df-cos
    @0
    cc
    wcel
    #
    @6
    @7
    @2
    @5
    @7
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    ci
    cc
    wcel
    @7
    @8
    ax-icn
    ci
    @0
    mulcl
    mpan
    @1
    efcl
    syl
    @7
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    @3
    cc
    wcel
    @7
    @9
    negicn
    @3
    @0
    mulcl
    mpan
    @4
    efcl
    syl
    addcld
    halfcld
    fmpti
end
