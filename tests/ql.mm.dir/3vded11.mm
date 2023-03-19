include "wi1.mm"
include "wt.mm"
include "le1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-t.mm"
include "ancom.mm"
include "anor2.mm"
include "ax-r2.mm"
include "lor.mm"
include "ax-r1.mm"
include "ax-a3.mm"
include "3tr.mm"
include "leo.mm"
include "df-i1.mm"
include "lbtr.mm"
include "lelan.mm"
include "lelor.mm"
include "lel2or.mm"
include "bltr.mm"
include "lebi.mm"
include "u1lemle2.mm"

theorem 3vded11
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume 3vded11.1: |- b =< ( c ->1 ( b ->1 a ) )


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
    wvb
    wvc
    wn
    #
    wvc
    wvb
    wn
    #
    wa
    #
    wo
    #
    wo
    #
    @1
    wt
    wvb
    @2
    wo
    #
    @7
    wn
    #
    wo
    #
    @7
    @4
    wo
    #
    @6
    @7
    df-t
    @10
    @9
    @4
    @8
    @7
    @4
    @3
    wvc
    wa
    @8
    wvc
    @3
    ancom
    wvb
    wvc
    anor2
    ax-r2
    lor
    ax-r1
    wvb
    @2
    @4
    ax-a3
    3tr
    wvb
    @1
    @5
    3vded11.1
    @5
    @2
    wvc
    @0
    wa
    #
    wo
    #
    @1
    @4
    @11
    @2
    @3
    @0
    wvc
    @3
    @3
    wvb
    wva
    wa
    #
    wo
    #
    @0
    @3
    @13
    leo
    @0
    @14
    wvb
    wva
    df-i1
    ax-r1
    lbtr
    lelan
    lelor
    @1
    @12
    wvc
    @0
    df-i1
    ax-r1
    lbtr
    lel2or
    bltr
    lebi
    u1lemle2
end
