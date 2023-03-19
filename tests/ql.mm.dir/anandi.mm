include "wa.mm"
include "anidm.mm"
include "ax-r1.mm"
include "ran.mm"
include "an4.mm"
include "ax-r2.mm"

theorem anandi
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( a ^ ( b ^ c ) ) = ( ( a ^ b ) ^ ( a ^ c ) )

  proof
    wva
    wvb
    wvc
    wa
    #
    wa
    wva
    wva
    wa
    #
    @0
    wa
    wva
    wvb
    wa
    wva
    wvc
    wa
    wa
    wva
    @1
    @0
    @1
    wva
    wva
    anidm
    ax-r1
    ran
    wva
    wva
    wvb
    wvc
    an4
    ax-r2
end
