include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ancom.mm"
include "comorr.mm"
include "comcom3.mm"
include "comcom4.mm"
include "comcom.mm"
include "fh2r.mm"
include "ax-r2.mm"

theorem marsdenlem1
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume marsden.1: |- a C b
  assume marsden.2: |- b C c
  assume marsden.3: |- c C d
  assume marsden.4: |- d C a


  assert |- ( ( a v b ) ^ ( a ' v d ' ) ) = ( ( a ' ^ ( a v b ) ) v ( d ' ^ ( a v b ) ) )

  proof
    wva
    wvb
    wo
    #
    wva
    wn
    #
    wvd
    wn
    #
    wo
    #
    wa
    @3
    @0
    wa
    @1
    @0
    wa
    @2
    @0
    wa
    wo
    @0
    @3
    ancom
    @1
    @0
    @2
    wva
    @0
    wva
    wvb
    comorr
    comcom3
    @2
    @1
    wvd
    wva
    marsden.4
    comcom4
    comcom
    fh2r
    ax-r2
end
