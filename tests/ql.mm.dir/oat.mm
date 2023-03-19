include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "leor.mm"
include "oml.mm"
include "ax-r1.mm"
include "lea.mm"
include "ler2an.mm"
include "lelor.mm"
include "bltr.mm"
include "letr.mm"
include "ax-a1.mm"
include "ax-r5.mm"
include "df-i1.mm"
include "ax-r2.mm"
include "lbtr.mm"

theorem oat
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume oat.1: |- ( a ' ^ ( a v b ) ) =< c


  assert |- b =< ( a ' ->1 c )

  proof
    wvb
    wva
    wva
    wn
    #
    wvc
    wa
    #
    wo
    #
    @0
    wvc
    wi1
    #
    wvb
    wva
    wvb
    wo
    #
    @2
    wvb
    wva
    leor
    @4
    wva
    @0
    @4
    wa
    #
    wo
    #
    @2
    @6
    @4
    wva
    wvb
    oml
    ax-r1
    @5
    @1
    wva
    @5
    @0
    wvc
    @0
    @4
    lea
    oat.1
    ler2an
    lelor
    bltr
    letr
    @2
    @0
    wn
    #
    @1
    wo
    #
    @3
    wva
    @7
    @1
    wva
    ax-a1
    ax-r5
    @3
    @8
    @0
    wvc
    df-i1
    ax-r1
    ax-r2
    lbtr
end
