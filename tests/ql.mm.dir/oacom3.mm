include "wo.mm"
include "wi2.mm"
include "wa.mm"
include "wi0.mm"
include "comcom.mm"
include "ancom.mm"
include "bctr.mm"
include "gsth2.mm"
include "wn.mm"
include "df-i0.mm"
include "ran.mm"
include "oath1.mm"
include "3tr.mm"
include "cbtr.mm"

theorem oacom3
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oacom3.1: |- ( d ^ ( a ->2 b ) ) C ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )
  assume oacom3.2: |- d C ( a ->2 b )


  assert |- d C ( ( a ->2 b ) ^ ( a ->2 c ) )

  proof
    wvd
    wvb
    wvc
    wo
    #
    wva
    wvb
    wi2
    #
    wva
    wvc
    wi2
    wa
    #
    wi0
    #
    @1
    wa
    #
    @2
    @4
    wvd
    @3
    @1
    wvd
    wvd
    @1
    oacom3.2
    comcom
    @1
    wvd
    wa
    #
    @3
    @5
    wvd
    @1
    wa
    @3
    @1
    wvd
    ancom
    oacom3.1
    bctr
    comcom
    gsth2
    comcom
    @4
    @0
    wn
    @2
    wo
    #
    @1
    wa
    @1
    @6
    wa
    @2
    @3
    @6
    @1
    @0
    @2
    df-i0
    ran
    @6
    @1
    ancom
    wva
    wvb
    wvc
    oath1
    3tr
    cbtr
end
