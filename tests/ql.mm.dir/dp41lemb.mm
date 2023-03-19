include "wo.mm"
include "wa.mm"
include "ancom.mm"
include "tr.mm"
include "leor.mm"
include "leror.mm"
include "leo.mm"
include "le2an.mm"
include "bltr.mm"
include "df2le2.mm"
include "cm.mm"
include "anass.mm"

theorem dp41lemb
  param wvp: term p
  param wva0: term a0
  param wva1: term a1
  param wva2: term a2
  param wvb0: term b0
  param wvb1: term b1
  param wvb2: term b2
  param wvc0: term c0
  param wvc1: term c1
  param wvc2: term c2
  param wvp2: term p2
  assume dp41lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp41lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp41lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp41lem.4: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )
  assume dp41lem.5: |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )
  assume dp41lem.6: |- p2 =< ( a2 v b2 )


  assert |- c2 = ( ( c2 ^ ( ( a0 v b0 ) v b1 ) ) ^ ( ( a0 v a1 ) v b1 ) )

  proof
    wvc2
    wvc2
    wva0
    wvb0
    wo
    #
    wvb1
    wo
    #
    wva0
    wva1
    wo
    #
    wvb1
    wo
    #
    wa
    #
    wa
    #
    wvc2
    @1
    wa
    @3
    wa
    #
    @5
    wvc2
    wvc2
    @4
    wvc2
    wvb0
    wvb1
    wo
    #
    @2
    wa
    #
    @4
    wvc2
    @2
    @7
    wa
    @8
    dp41lem.3
    @2
    @7
    ancom
    tr
    @7
    @1
    @2
    @3
    wvb0
    @0
    wvb1
    wvb0
    wva0
    leor
    leror
    @2
    wvb1
    leo
    le2an
    bltr
    df2le2
    cm
    @6
    @5
    wvc2
    @1
    @3
    anass
    cm
    tr
end
