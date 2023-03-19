include "wo.mm"
include "wa.mm"
include "fh1.mm"
include "ancom.mm"
include "2or.mm"
include "3tr1.mm"

theorem fh1r
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- ( ( b v c ) ^ a ) = ( ( b ^ a ) v ( c ^ a ) )

  proof
    wva
    wvb
    wvc
    wo
    #
    wa
    wva
    wvb
    wa
    #
    wva
    wvc
    wa
    #
    wo
    @0
    wva
    wa
    wvb
    wva
    wa
    #
    wvc
    wva
    wa
    #
    wo
    wva
    wvb
    wvc
    fh.1
    fh.2
    fh1
    @0
    wva
    ancom
    @3
    @1
    @4
    @2
    wvb
    wva
    ancom
    wvc
    wva
    ancom
    2or
    3tr1
end
