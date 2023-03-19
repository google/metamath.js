include "tb.mm"
include "wo.mm"
include "wa.mm"
include "lea.mm"
include "mlaconjo.mm"
include "ler2an.mm"
include "bicom.mm"
include "ax-a2.mm"
include "2an.mm"
include "bltr.mm"
include "ler2or.mm"
include "ledi.mm"
include "lebi.mm"

theorem distid
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) = ( ( ( a == b ) ^ ( a == c ) ) v ( ( a == b ) ^ ( b == c ) ) )

  proof
    wva
    wvb
    tb
    #
    wva
    wvc
    tb
    #
    wvb
    wvc
    tb
    #
    wo
    #
    wa
    #
    @0
    @1
    wa
    #
    @0
    @2
    wa
    #
    wo
    @4
    @5
    @6
    @4
    @0
    @1
    @0
    @3
    lea
    #
    wva
    wvb
    wvc
    mlaconjo
    ler2an
    @4
    @0
    @2
    @7
    @4
    wvb
    wva
    tb
    #
    @2
    @1
    wo
    #
    wa
    @2
    @0
    @8
    @3
    @9
    wva
    wvb
    bicom
    @1
    @2
    ax-a2
    2an
    wvb
    wva
    wvc
    mlaconjo
    bltr
    ler2an
    ler2or
    @0
    @1
    @2
    ledi
    lebi
end
