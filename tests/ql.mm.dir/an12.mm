include "wa.mm"
include "ancom.mm"
include "ran.mm"
include "anass.mm"
include "3tr2.mm"

theorem an12
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a ^ ( b ^ c ) ) = ( b ^ ( a ^ c ) )

  proof
    wva
    wvb
    wa
    #
    wvc
    wa
    wvb
    wva
    wa
    #
    wvc
    wa
    wva
    wvb
    wvc
    wa
    wa
    wvb
    wva
    wvc
    wa
    wa
    @0
    @1
    wvc
    wva
    wvb
    ancom
    ran
    wva
    wvb
    wvc
    anass
    wvb
    wva
    wvc
    anass
    3tr2
end
