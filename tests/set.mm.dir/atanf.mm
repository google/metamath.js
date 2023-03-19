include "cc.mm"
include "ci.mm"
include "cneg.mm"
include "cpr.mm"
include "cdif.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "clog.mm"
include "cfv.mm"
include "caddc.mm"
include "catan.mm"
include "df-atan.mm"
include "wcel.mm"
include "cdm.mm"
include "ovex.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "ax-icn.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "ax-1cn.mm"
include "cc0.mm"
include "wne.mm"
include "atandm2.mm"
include "simp1bi.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcl.mm"
include "simp2bi.mm"
include "logcld.mm"
include "addcl.mm"
include "simp3bi.mm"
include "subcld.mm"
include "sylbir.mm"
include "fmpti.mm"

theorem atanf
  let vx: setvar x


  assert |- arctan : ( CC \ { -u _i , _i } ) --> CC

  proof
    vx
    cc
    ci
    cneg
    ci
    cpr
    cdif
    #
    cc
    ci
    c2
    cdiv
    co
    #
    c1
    ci
    vx
    cv
    #
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @3
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    catan
    vx
    df-atan
    #
    @2
    @0
    wcel
    @2
    catan
    cdm
    #
    wcel
    #
    @9
    cc
    wcel
    #
    @11
    @0
    @2
    vx
    @0
    @9
    catan
    @1
    @8
    cmul
    ovex
    @10
    dmmpti
    eleq2i
    @12
    @1
    cc
    wcel
    #
    @8
    cc
    wcel
    @13
    ci
    cc
    wcel
    #
    @14
    ax-icn
    ci
    halfcl
    ax-mp
    @12
    @5
    @7
    @12
    @4
    @12
    c1
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @4
    cc
    wcel
    ax-1cn
    @12
    @15
    @2
    cc
    wcel
    #
    @17
    ax-icn
    @12
    @18
    @4
    cc0
    wne
    #
    @6
    cc0
    wne
    #
    @2
    atandm2
    #
    simp1bi
    ci
    @2
    mulcl
    sylancr
    #
    c1
    @3
    subcl
    sylancr
    @12
    @18
    @19
    @20
    @21
    simp2bi
    logcld
    @12
    @6
    @12
    @16
    @17
    @6
    cc
    wcel
    ax-1cn
    @22
    c1
    @3
    addcl
    sylancr
    @12
    @18
    @19
    @20
    @21
    simp3bi
    logcld
    subcld
    @1
    @8
    mulcl
    sylancr
    sylbir
    fmpti
end
