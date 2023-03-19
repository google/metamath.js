include "wa.mm"
include "wleran.mm"
include "ancom.mm"
include "bi1.mm"
include "wle3tr1.mm"
include "wletr.mm"

theorem wle2an
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume wle2.1: |- ( a =<2 b ) = 1
  assume wle2.2: |- ( c =<2 d ) = 1


  assert |- ( ( a ^ c ) =<2 ( b ^ d ) ) = 1

  proof
    wva
    wvc
    wa
    wvb
    wvc
    wa
    #
    wvb
    wvd
    wa
    #
    wva
    wvb
    wvc
    wle2.1
    wleran
    wvc
    wvb
    wa
    #
    wvd
    wvb
    wa
    #
    @0
    @1
    wvc
    wvd
    wvb
    wle2.2
    wleran
    @0
    @2
    wvb
    wvc
    ancom
    bi1
    @1
    @3
    wvb
    wvd
    ancom
    bi1
    wle3tr1
    wletr
end
