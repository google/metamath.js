include "wa.mm"
include "wo.mm"
include "fh4.mm"
include "ax-a2.mm"
include "2an.mm"
include "3tr1.mm"

theorem fh4r
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- ( ( a ^ c ) v b ) = ( ( a v b ) ^ ( c v b ) )

  proof
    wvb
    wva
    wvc
    wa
    #
    wo
    wvb
    wva
    wo
    #
    wvb
    wvc
    wo
    #
    wa
    @0
    wvb
    wo
    wva
    wvb
    wo
    #
    wvc
    wvb
    wo
    #
    wa
    wva
    wvb
    wvc
    fh.1
    fh.2
    fh4
    @0
    wvb
    ax-a2
    @3
    @1
    @4
    @2
    wva
    wvb
    ax-a2
    wvc
    wvb
    ax-a2
    2an
    3tr1
end
