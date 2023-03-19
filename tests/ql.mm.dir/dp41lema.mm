include "wo.mm"
include "wa.mm"
include "cm.mm"
include "bltr.mm"
include "df2le2.mm"
include "tr.mm"
include "dp34.mm"

theorem dp41lema
  let wvp: term p
  let wva0: term a0
  let wva1: term a1
  let wva2: term a2
  let wvb0: term b0
  let wvb1: term b1
  let wvb2: term b2
  let wvc0: term c0
  let wvc1: term c1
  let wvc2: term c2
  let wvp2: term p2
  assume dp41lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp41lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp41lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp41lem.4: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )
  assume dp41lem.5: |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )
  assume dp41lem.6: |- p2 =< ( a2 v b2 )


  assert |- ( ( a0 v b0 ) ^ ( a1 v b1 ) ) =< ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) )

  proof
    wva0
    wvb0
    wo
    wva1
    wvb1
    wo
    wa
    #
    wvp
    wva0
    wvb1
    wo
    wvc2
    wvc0
    wvc1
    wo
    wa
    wo
    @0
    @0
    wva2
    wvb2
    wo
    #
    wa
    #
    wvp
    @2
    @0
    @0
    @1
    @0
    wvp2
    @1
    wvp2
    @0
    dp41lem.5
    cm
    dp41lem.6
    bltr
    df2le2
    cm
    wvp
    @2
    dp41lem.4
    cm
    tr
    wvp
    wva0
    wva1
    wva2
    wvb0
    wvb1
    wvb2
    wvc0
    wvc1
    wvc2
    dp41lem.1
    dp41lem.2
    dp41lem.3
    dp41lem.4
    dp34
    bltr
end
