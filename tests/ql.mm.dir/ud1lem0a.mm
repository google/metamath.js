include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "lan.mm"
include "lor.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem ud1lem0a
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume ud1lem0a.1: |- a = b


  assert |- ( c ->1 a ) = ( c ->1 b )

  proof
    wvc
    wn
    #
    wvc
    wva
    wa
    #
    wo
    @0
    wvc
    wvb
    wa
    #
    wo
    wvc
    wva
    wi1
    wvc
    wvb
    wi1
    @1
    @2
    @0
    wva
    wvb
    wvc
    ud1lem0a.1
    lan
    lor
    wvc
    wva
    df-i1
    wvc
    wvb
    df-i1
    3tr1
end
