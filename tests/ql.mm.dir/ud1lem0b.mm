include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "ax-r4.mm"
include "ran.mm"
include "2or.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem ud1lem0b
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ud1lem0a.1: |- a = b


  assert |- ( a ->1 c ) = ( b ->1 c )

  proof
    wva
    wn
    #
    wva
    wvc
    wa
    #
    wo
    wvb
    wn
    #
    wvb
    wvc
    wa
    #
    wo
    wva
    wvc
    wi1
    wvb
    wvc
    wi1
    @0
    @2
    @1
    @3
    wva
    wvb
    ud1lem0a.1
    ax-r4
    wva
    wvb
    wvc
    ud1lem0a.1
    ran
    2or
    wva
    wvc
    df-i1
    wvb
    wvc
    df-i1
    3tr1
end
