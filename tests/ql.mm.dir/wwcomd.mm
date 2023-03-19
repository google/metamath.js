include "wo.mm"
include "wn.mm"
include "wa.mm"
include "df-c2.mm"
include "oran.mm"
include "ax-a2.mm"
include "anor2.mm"
include "ax-r1.mm"
include "con3.mm"
include "2an.mm"
include "ax-r4.mm"
include "3tr1.mm"
include "ax-r2.mm"
include "con1.mm"

theorem wwcomd
  let wva: term a
  let wvb: term b
  assume wwcomd.1: |- a ' C b


  assert |- a = ( ( a v b ) ^ ( a v b ' ) )

  proof
    wva
    wva
    wvb
    wo
    #
    wva
    wvb
    wn
    #
    wo
    #
    wa
    #
    wva
    wn
    #
    @4
    wvb
    wa
    #
    @4
    @1
    wa
    #
    wo
    #
    @3
    wn
    #
    @4
    wvb
    wwcomd.1
    df-c2
    @6
    @5
    wo
    @6
    wn
    #
    @5
    wn
    #
    wa
    #
    wn
    @7
    @8
    @6
    @5
    oran
    @5
    @6
    ax-a2
    @3
    @11
    @0
    @9
    @2
    @10
    wva
    wvb
    oran
    @2
    @5
    @5
    @2
    wn
    wva
    wvb
    anor2
    ax-r1
    con3
    2an
    ax-r4
    3tr1
    ax-r2
    con1
end
