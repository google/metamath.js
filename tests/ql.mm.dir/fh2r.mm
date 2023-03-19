include "wo.mm"
include "wa.mm"
include "fh2.mm"
include "ancom.mm"
include "2or.mm"
include "3tr1.mm"

theorem fh2r
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- ( ( a v c ) ^ b ) = ( ( a ^ b ) v ( c ^ b ) )

  proof
    wvb
    wva
    wvc
    wo
    #
    wa
    wvb
    wva
    wa
    #
    wvb
    wvc
    wa
    #
    wo
    @0
    wvb
    wa
    wva
    wvb
    wa
    #
    wvc
    wvb
    wa
    #
    wo
    wva
    wvb
    wvc
    fh.1
    fh.2
    fh2
    @0
    wvb
    ancom
    @3
    @1
    @4
    @2
    wva
    wvb
    ancom
    wvc
    wvb
    ancom
    2or
    3tr1
end
