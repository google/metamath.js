include "wa.mm"
include "wo.mm"
include "fh3r.mm"
include "ancom.mm"
include "ax-r5.mm"
include "3tr1.mm"

theorem fh3rc
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- ( ( c ^ b ) v a ) = ( ( c v a ) ^ ( b v a ) )

  proof
    wvb
    wvc
    wa
    #
    wva
    wo
    wvb
    wva
    wo
    #
    wvc
    wva
    wo
    #
    wa
    wvc
    wvb
    wa
    #
    wva
    wo
    @2
    @1
    wa
    wva
    wvb
    wvc
    fh.1
    fh.2
    fh3r
    @3
    @0
    wva
    wvc
    wvb
    ancom
    ax-r5
    @2
    @1
    ancom
    3tr1
end
