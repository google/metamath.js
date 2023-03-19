include "wi1.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "lea.mm"
include "ax-a1.mm"
include "lbtr.mm"
include "leo.mm"
include "letr.mm"
include "ud1lem0c.mm"
include "df-i1.mm"
include "le3tr1.mm"
include "lecom.mm"
include "comcom6.mm"

theorem u1lemc6
  let wva: term a
  let wvb: term b


  assert |- ( a ->1 b ) C ( a ' ->1 b )

  proof
    wva
    wvb
    wi1
    #
    wva
    wn
    #
    wvb
    wi1
    #
    @0
    wn
    #
    @2
    wva
    @1
    wvb
    wn
    wo
    #
    wa
    #
    @1
    wn
    #
    @1
    wvb
    wa
    #
    wo
    #
    @3
    @2
    @5
    @6
    @8
    @5
    wva
    @6
    wva
    @4
    lea
    wva
    ax-a1
    lbtr
    @6
    @7
    leo
    letr
    wva
    wvb
    ud1lem0c
    @1
    wvb
    df-i1
    le3tr1
    lecom
    comcom6
end
