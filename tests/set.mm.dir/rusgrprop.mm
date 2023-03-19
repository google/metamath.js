include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "crgr.mm"
include "cv.mm"
include "copab.mm"
include "df-rusgr.mm"
include "breqi.mm"
include "brabv.mm"
include "sylbi.mm"
include "isrusgr.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem rusgrprop
  let cG: class G
  let cK: class K
  let vg: setvar g
  let vk: setvar k


  assert |- ( G RegUSGraph K -> ( G e. USGraph /\ G RegGraph K ) )

  proof
    cG
    cvv
    wcel
    cK
    cvv
    wcel
    wa
    #
    cG
    cK
    crusgr
    wbr
    #
    cG
    cusgr
    wcel
    cG
    cK
    crgr
    wbr
    wa
    #
    @1
    cG
    cK
    vg
    cv
    #
    cusgr
    wcel
    @3
    vk
    cv
    crgr
    wbr
    wa
    #
    vg
    vk
    copab
    #
    wbr
    @0
    cG
    cK
    crusgr
    @5
    vg
    vk
    df-rusgr
    breqi
    @4
    vg
    vk
    cG
    cK
    brabv
    sylbi
    @0
    @1
    @2
    cG
    cK
    cvv
    cvv
    isrusgr
    biimpd
    mpcom
end
