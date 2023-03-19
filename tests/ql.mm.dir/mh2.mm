include "comcom.mm"
include "mh.mm"

theorem mh2
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume marsden.1: |- a C b
  assume marsden.2: |- b C c
  assume marsden.3: |- c C d
  assume marsden.4: |- d C a


  assert |- ( ( a v b ) ^ ( c v d ) ) = ( ( ( a ^ c ) v ( a ^ d ) ) v ( ( b ^ c ) v ( b ^ d ) ) )

  proof
    wva
    wvc
    wvb
    wvd
    marsden.1
    wvd
    wva
    marsden.4
    comcom
    wvb
    wvc
    marsden.2
    comcom
    marsden.3
    mh
end
