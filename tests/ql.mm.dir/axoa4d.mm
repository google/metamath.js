include "wa.mm"
include "wi1.mm"
include "wo.mm"
include "wn.mm"
include "oa4dcom.mm"
include "ax-r1.mm"
include "axoa4.mm"
include "oa4ctod.mm"
include "bltr.mm"

theorem axoa4d
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d


  assert |- ( a ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) =< ( b ' ->1 d )

  proof
    wva
    wva
    wvb
    wa
    wva
    wvd
    wi1
    #
    wvb
    wvd
    wi1
    #
    wa
    wo
    wva
    wvc
    wa
    @0
    wvc
    wvd
    wi1
    #
    wa
    wo
    #
    wvb
    wvc
    wa
    @1
    @2
    wa
    wo
    #
    wa
    wo
    wa
    #
    wva
    wvb
    wva
    wa
    @1
    @0
    wa
    wo
    @4
    @3
    wa
    wo
    wa
    #
    wvb
    wn
    wvd
    wi1
    @6
    @5
    wvb
    wva
    wvc
    wvd
    oa4dcom
    ax-r1
    wvb
    wva
    wvc
    wvd
    wvb
    wva
    wvc
    wvd
    axoa4
    oa4ctod
    bltr
end
