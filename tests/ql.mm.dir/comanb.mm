include "wa.mm"
include "tb.mm"
include "wo.mm"
include "wn.mm"
include "wi1.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "lecon.mm"
include "leror.mm"
include "comanblem1.mm"
include "df-i1.mm"
include "comanblem2.mm"
include "lor.mm"
include "ax-r2.mm"
include "le3tr1.mm"
include "i1com.mm"

theorem comanb
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( a ^ b ) C ( ( a == c ) ^ ( b == c ) )

  proof
    wva
    wvb
    wa
    #
    wva
    wvc
    tb
    wvb
    wvc
    tb
    wa
    #
    wva
    wvc
    wo
    #
    wn
    #
    @0
    wvc
    wa
    #
    wo
    #
    wvb
    wvc
    wi1
    #
    wa
    #
    @0
    wn
    #
    @4
    wo
    #
    @1
    @0
    @1
    wi1
    #
    @7
    @5
    @9
    @5
    @6
    lea
    @3
    @8
    @4
    @0
    @2
    @0
    wva
    @2
    wva
    wvb
    lea
    wva
    wvc
    leo
    letr
    lecon
    leror
    letr
    wva
    wvb
    wvc
    comanblem1
    @10
    @8
    @0
    @1
    wa
    #
    wo
    @9
    @0
    @1
    df-i1
    @11
    @4
    @8
    wva
    wvb
    wvc
    comanblem2
    lor
    ax-r2
    le3tr1
    i1com
end
