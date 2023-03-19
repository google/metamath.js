include "wo.mm"
include "wa.mm"
include "anass.mm"
include "anabs.mm"
include "ran.mm"
include "ancom.mm"
include "leor.mm"
include "mlduali.mm"
include "tr.mm"
include "lan.mm"
include "3tr2.mm"

theorem modexp
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a ^ ( b v c ) ) = ( a ^ ( b v ( c ^ ( a v b ) ) ) )

  proof
    wva
    wva
    wvb
    wo
    #
    wa
    #
    wvb
    wvc
    wo
    #
    wa
    wva
    @0
    @2
    wa
    #
    wa
    wva
    @2
    wa
    wva
    wvb
    wvc
    @0
    wa
    wo
    #
    wa
    wva
    @0
    @2
    anass
    @1
    wva
    @2
    wva
    wvb
    anabs
    ran
    @3
    @4
    wva
    @3
    @2
    @0
    wa
    @4
    @0
    @2
    ancom
    wvb
    wvc
    @0
    wvb
    wva
    leor
    mlduali
    tr
    lan
    3tr2
end
