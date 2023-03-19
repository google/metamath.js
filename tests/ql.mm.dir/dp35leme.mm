include "wo.mm"
include "wa.mm"
include "leor.mm"
include "lor.mm"
include "bile.mm"
include "le2an.mm"
include "ancom.mm"
include "anass.mm"
include "cm.mm"
include "tr.mm"
include "leo.mm"
include "mlduali.mm"
include "3tr1.mm"
include "dp35lemf.mm"
include "bltr.mm"
include "letr.mm"

theorem dp35leme
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
  let wvp0: term p0
  assume dp35lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp35lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp35lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp35lem.4: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume dp35lem.5: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )


  assert |- ( b0 ^ ( a0 v p0 ) ) =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) )

  proof
    wvb0
    wva0
    wvp0
    wo
    #
    wa
    wva0
    wvb0
    wo
    #
    wva0
    wva1
    wvb1
    wo
    #
    wva2
    wvb2
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wva0
    wvb0
    wvb1
    wvc2
    wvc0
    wvc1
    wo
    wa
    wo
    wa
    wo
    #
    wvb0
    @1
    @0
    @5
    wvb0
    wva0
    leor
    @0
    @5
    wvp0
    @4
    wva0
    dp35lem.4
    lor
    bile
    le2an
    @6
    wva0
    wvp
    wo
    #
    @7
    wva0
    @4
    @1
    wa
    #
    wo
    #
    wva0
    @1
    @2
    wa
    @3
    wa
    #
    wo
    @6
    @8
    @9
    @11
    wva0
    @9
    @1
    @4
    wa
    #
    @11
    @4
    @1
    ancom
    @11
    @12
    @1
    @2
    @3
    anass
    cm
    tr
    lor
    @6
    @5
    @1
    wa
    @10
    @1
    @5
    ancom
    wva0
    @4
    @1
    wva0
    wvb0
    leo
    mlduali
    tr
    wvp
    @11
    wva0
    dp35lem.5
    lor
    3tr1
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
    wvp0
    dp35lem.1
    dp35lem.2
    dp35lem.3
    dp35lem.4
    dp35lem.5
    dp35lemf
    bltr
    letr
end
