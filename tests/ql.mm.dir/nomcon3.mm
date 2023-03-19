include "wid2.mm"
include "wn.mm"
include "wid1.mm"
include "wid3.mm"
include "wid4.mm"
include "nomcon2.mm"
include "nomb32.mm"
include "nomb41.mm"
include "3tr1.mm"

theorem nomcon3
  param wva: term a
  param wvb: term b


  assert |- ( a ==3 b ) = ( b ' ==4 a ' )

  proof
    wvb
    wva
    wid2
    wva
    wn
    #
    wvb
    wn
    #
    wid1
    wva
    wvb
    wid3
    @1
    @0
    wid4
    wvb
    wva
    nomcon2
    wva
    wvb
    nomb32
    @1
    @0
    nomb41
    3tr1
end
