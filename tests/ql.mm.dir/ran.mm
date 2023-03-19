include "wa.mm"
include "lan.mm"
include "ancom.mm"
include "3tr1.mm"

theorem ran
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume ran.1: |- a = b


  assert |- ( a ^ c ) = ( b ^ c )

  proof
    wvc
    wva
    wa
    wvc
    wvb
    wa
    wva
    wvc
    wa
    wvb
    wvc
    wa
    wva
    wvb
    wvc
    ran.1
    lan
    wva
    wvc
    ancom
    wvb
    wvc
    ancom
    3tr1
end
