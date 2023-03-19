include "wn.mm"
include "wa.mm"
include "tb.mm"
include "comanb.mm"
include "conb.mm"
include "2an.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem comanbn
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a ' ^ b ' ) C ( ( a == c ) ^ ( b == c ) )

  proof
    wva
    wn
    #
    wvb
    wn
    #
    wa
    @0
    wvc
    wn
    #
    tb
    #
    @1
    @2
    tb
    #
    wa
    #
    wva
    wvc
    tb
    #
    wvb
    wvc
    tb
    #
    wa
    #
    @0
    @1
    @2
    comanb
    @8
    @5
    @6
    @3
    @7
    @4
    wva
    wvc
    conb
    wvb
    wvc
    conb
    2an
    ax-r1
    cbtr
end
