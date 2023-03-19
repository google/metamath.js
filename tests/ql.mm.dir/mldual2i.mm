include "wa.mm"
include "wo.mm"
include "mldual.mm"
include "lear.mm"
include "leid.mm"
include "ler2an.mm"
include "lebi.mm"
include "lor.mm"
include "lan.mm"
include "3tr2.mm"

theorem mldual2i
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume mlduali.1: |- a =< c


  assert |- ( c ^ ( b v a ) ) = ( ( c ^ b ) v a )

  proof
    wvc
    wvb
    wvc
    wva
    wa
    #
    wo
    #
    wa
    wvc
    wvb
    wa
    #
    @0
    wo
    wvc
    wvb
    wva
    wo
    #
    wa
    @2
    wva
    wo
    wvc
    wvb
    wva
    mldual
    @1
    @3
    wvc
    @0
    wva
    wvb
    @0
    wva
    wvc
    wva
    lear
    wva
    wvc
    wva
    mlduali.1
    wva
    leid
    ler2an
    lebi
    #
    lor
    lan
    @0
    wva
    @2
    @4
    lor
    3tr2
end
