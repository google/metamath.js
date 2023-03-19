include "wa.mm"
include "wi3.mm"
include "i3id.mm"
include "ancom.mm"
include "ri3.mm"
include "bi1.mm"
include "wwbmp.mm"

theorem i3ancom
  param wva: term a
  param wvb: term b


  assert |- ( ( a ^ b ) ->3 ( b ^ a ) ) = 1

  proof
    wvb
    wva
    wa
    #
    @0
    wi3
    #
    wva
    wvb
    wa
    #
    @0
    wi3
    #
    @0
    i3id
    @1
    @3
    @0
    @2
    @0
    wvb
    wva
    ancom
    ri3
    bi1
    wwbmp
end
