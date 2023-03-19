include "wi1.mm"
include "wt.mm"
include "le1.mm"
include "wn.mm"
include "wo.mm"
include "df-t.mm"
include "wa.mm"
include "an1.mm"
include "ax-r1.mm"
include "u1lemle1.mm"
include "lan.mm"
include "ax-r2.mm"
include "bltr.mm"
include "lecon.mm"
include "leo.mm"
include "df-i1.mm"
include "lbtr.mm"
include "letr.mm"
include "lel2or.mm"
include "lebi.mm"
include "u1lemle2.mm"

theorem 3vded12
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume 3vded12.1: |- ( a ^ ( c ->1 a ) ) =< ( c ->1 ( b ->1 a ) )
  assume 3vded12.2: |- c =< a


  assert |- c =< ( b ->1 a )

  proof
    wvc
    wvb
    wva
    wi1
    #
    wvc
    @0
    wi1
    #
    wt
    @1
    le1
    wt
    wva
    wva
    wn
    #
    wo
    @1
    wva
    df-t
    wva
    @1
    @2
    wva
    wva
    wvc
    wva
    wi1
    #
    wa
    #
    @1
    wva
    wva
    wt
    wa
    #
    @4
    @5
    wva
    wva
    an1
    ax-r1
    @4
    @5
    @3
    wt
    wva
    wvc
    wva
    3vded12.2
    u1lemle1
    lan
    ax-r1
    ax-r2
    3vded12.1
    bltr
    @2
    wvc
    wn
    #
    @1
    wvc
    wva
    3vded12.2
    lecon
    @6
    @6
    wvc
    @0
    wa
    #
    wo
    #
    @1
    @6
    @7
    leo
    @1
    @8
    wvc
    @0
    df-i1
    ax-r1
    lbtr
    letr
    lel2or
    bltr
    lebi
    u1lemle2
end
