include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wcomcom4.mm"
include "wdf-c2.mm"
include "ax-a1.mm"
include "bi1.mm"
include "w2an.mm"
include "w2or.mm"
include "w3tr1.mm"
include "wdf-c1.mm"

theorem wcomcom5
  let wva: term a
  let wvb: term b
  assume wcomcom5.1: |- C ( a ' , b ' ) = 1


  assert |- C ( a , b ) = 1

  proof
    wva
    wvb
    wva
    wn
    #
    wn
    #
    @1
    wvb
    wn
    #
    wn
    #
    wa
    #
    @1
    @3
    wn
    #
    wa
    #
    wo
    wva
    wva
    wvb
    wa
    #
    wva
    @2
    wa
    #
    wo
    @1
    @3
    @0
    @2
    wcomcom5.1
    wcomcom4
    wdf-c2
    wva
    @1
    wva
    ax-a1
    bi1
    #
    @7
    @4
    @8
    @6
    wva
    @1
    wvb
    @3
    @9
    wvb
    @3
    wvb
    ax-a1
    bi1
    w2an
    wva
    @1
    @2
    @5
    @9
    @2
    @5
    @2
    ax-a1
    bi1
    w2an
    w2or
    w3tr1
    wdf-c1
end
