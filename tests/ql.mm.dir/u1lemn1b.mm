include "wi1.mm"
include "wf.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ax-a1.mm"
include "u1lemnab.mm"
include "ax-r1.mm"
include "2or.mm"
include "or0.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem u1lemn1b
  let wva: term a
  let wvb: term b


  assert |- ( a ->1 b ) = ( ( a ->1 b ) ' ->1 b )

  proof
    wva
    wvb
    wi1
    #
    wf
    wo
    #
    @0
    wn
    #
    wn
    #
    @2
    wvb
    wa
    #
    wo
    @0
    @2
    wvb
    wi1
    @0
    @3
    wf
    @4
    @0
    ax-a1
    @4
    wf
    wva
    wvb
    u1lemnab
    ax-r1
    2or
    @1
    @0
    @0
    or0
    ax-r1
    @2
    wvb
    df-i1
    3tr1
end
