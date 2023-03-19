include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "wex.mm"
include "snex.mm"
include "eleq1.mm"
include "vsnid.mm"
include "spei.mm"
include "zfregcl.mm"
include "mp2.mm"
include "weq.mm"
include "velsn.mm"
include "wi.mm"
include "ax9.mm"
include "equcoms.mm"
include "com12.mm"
include "syl5bi.mm"
include "notbid.mm"
include "rspccv.mm"
include "mt2i.mm"
include "nsyli.mm"
include "con2d.mm"
include "ralrimiv.mm"
include "ralnex.mm"
include "sylib.mm"
include "mt2.mm"

theorem elirrv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. x e. x

  proof
    vx
    cv
    #
    @0
    wcel
    #
    vz
    cv
    #
    @0
    csn
    #
    wcel
    #
    wn
    #
    vz
    vy
    cv
    #
    wral
    #
    vy
    @3
    wrex
    #
    @3
    cvv
    wcel
    @6
    @3
    wcel
    #
    vy
    wex
    @8
    @0
    snex
    @9
    @0
    @3
    wcel
    #
    vy
    vx
    @6
    @0
    @3
    eleq1
    vx
    vsnid
    #
    spei
    vy
    vz
    @3
    cvv
    zfregcl
    mp2
    @1
    @7
    wn
    #
    vy
    @3
    wral
    @8
    wn
    @1
    @12
    vy
    @3
    @1
    @7
    @9
    @1
    @9
    @0
    @6
    wcel
    #
    @7
    @9
    vy
    vx
    weq
    #
    @1
    @13
    vy
    @0
    velsn
    @14
    @1
    @13
    @1
    @13
    wi
    vx
    vy
    vx
    vy
    vx
    ax9
    equcoms
    com12
    syl5bi
    @7
    @13
    @10
    @11
    @5
    @10
    wn
    vz
    @0
    @6
    vz
    vx
    weq
    @4
    @10
    @2
    @0
    @3
    eleq1
    notbid
    rspccv
    mt2i
    nsyli
    con2d
    ralrimiv
    @7
    vy
    @3
    ralnex
    sylib
    mt2
end
