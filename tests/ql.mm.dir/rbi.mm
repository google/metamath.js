include "tb.mm"
include "lbi.mm"
include "bicom.mm"
include "3tr1.mm"

theorem rbi
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume rbi.1: |- a = b


  assert |- ( a == c ) = ( b == c )

  proof
    wvc
    wva
    tb
    wvc
    wvb
    tb
    wva
    wvc
    tb
    wvb
    wvc
    tb
    wva
    wvb
    wvc
    rbi.1
    lbi
    wva
    wvc
    bicom
    wvb
    wvc
    bicom
    3tr1
end
