include "wcel.mm"
include "wa.mm"
include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "crgr.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "breq12.mm"
include "anbi12d.mm"
include "df-rusgr.mm"
include "brabga.mm"
include "biidd.mm"
include "bitrd.mm"

theorem isrusgr
  let cG: class G
  let cK: class K
  let cW: class W
  let cZ: class Z
  let vg: setvar g
  let vk: setvar k


  assert |- ( ( G e. W /\ K e. Z ) -> ( G RegUSGraph K <-> ( G e. USGraph /\ G RegGraph K ) ) )

  proof
    cG
    cW
    wcel
    cK
    cZ
    wcel
    wa
    #
    cG
    cK
    crusgr
    wbr
    cG
    cusgr
    wcel
    #
    cG
    cK
    crgr
    wbr
    #
    wa
    #
    @3
    vg
    cv
    #
    cusgr
    wcel
    #
    @4
    vk
    cv
    #
    crgr
    wbr
    #
    wa
    @3
    vg
    vk
    cG
    cK
    crusgr
    cW
    cZ
    @4
    cG
    wceq
    #
    @6
    cK
    wceq
    #
    wa
    @5
    @1
    @7
    @2
    @8
    @5
    @1
    wb
    @9
    @4
    cG
    cusgr
    eleq1
    adantr
    @4
    cG
    @6
    cK
    crgr
    breq12
    anbi12d
    vg
    vk
    df-rusgr
    brabga
    @0
    @3
    biidd
    bitrd
end
