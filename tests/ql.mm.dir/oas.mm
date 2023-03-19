include "wi1.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "oml.mm"
include "ax-r1.mm"
include "lea.mm"
include "ler2an.mm"
include "lelor.mm"
include "bltr.mm"
include "lelan.mm"
include "u1lemc1.mm"
include "comanr1.mm"
include "comcom6.mm"
include "fh2.mm"
include "u1lemaa.mm"
include "ancom.mm"
include "leo.mm"
include "df-i1.mm"
include "lbtr.mm"
include "letr.mm"
include "df2le2.mm"
include "ax-r2.mm"
include "2or.mm"
include "lear.mm"
include "lel2or.mm"

theorem oas
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume oas.1: |- ( a ' ^ ( a v b ) ) =< c


  assert |- ( ( a ->1 c ) ^ ( a v b ) ) =< c

  proof
    wva
    wvc
    wi1
    #
    wva
    wvb
    wo
    #
    wa
    #
    wva
    wvc
    wa
    #
    wva
    wn
    #
    wvc
    wa
    #
    wo
    #
    wvc
    @2
    @0
    wva
    @5
    wo
    #
    wa
    #
    @6
    @1
    @7
    @0
    @1
    wva
    @4
    @1
    wa
    #
    wo
    #
    @7
    @10
    @1
    wva
    wvb
    oml
    ax-r1
    @9
    @5
    wva
    @9
    @4
    wvc
    @4
    @1
    lea
    oas.1
    ler2an
    lelor
    bltr
    lelan
    @8
    @0
    wva
    wa
    #
    @0
    @5
    wa
    #
    wo
    @6
    wva
    @0
    @5
    wva
    wvc
    u1lemc1
    wva
    @5
    @4
    wvc
    comanr1
    comcom6
    fh2
    @11
    @3
    @12
    @5
    wva
    wvc
    u1lemaa
    @12
    @5
    @0
    wa
    @5
    @0
    @5
    ancom
    @5
    @0
    @5
    @4
    @0
    @4
    wvc
    lea
    @4
    @4
    @3
    wo
    #
    @0
    @4
    @3
    leo
    @0
    @13
    wva
    wvc
    df-i1
    ax-r1
    lbtr
    letr
    df2le2
    ax-r2
    2or
    ax-r2
    lbtr
    @3
    wvc
    @5
    wva
    wvc
    lear
    @4
    wvc
    lear
    lel2or
    letr
end
