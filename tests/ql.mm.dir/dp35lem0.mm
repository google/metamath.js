include "wo.mm"
include "wa.mm"
include "orcom.mm"
include "leid.mm"
include "bltr.mm"
include "dp35lema.mm"
include "letr.mm"
include "lelan.mm"
include "id.mm"
include "lea.mm"
include "mldual2i.mm"
include "tr.mm"
include "ancom.mm"
include "ror.mm"
include "lbtr.mm"
include "lear.mm"
include "lelor.mm"

theorem dp35lem0
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


  assert |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) ) =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) )

  proof
    wva0
    wva1
    wo
    #
    wvb0
    wva0
    wvp0
    wo
    wa
    #
    wvb1
    wo
    #
    wa
    #
    wvb1
    @0
    wa
    #
    @0
    wvc0
    wvc1
    wo
    #
    wa
    #
    wo
    #
    @5
    @4
    wo
    #
    @3
    @0
    wvb1
    @6
    wo
    #
    wa
    #
    @7
    @2
    @9
    @0
    @2
    wvb1
    @1
    wo
    #
    @9
    @2
    @11
    @11
    @1
    wvb1
    orcom
    @11
    leid
    bltr
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
    dp35lema
    letr
    lelan
    @10
    @0
    wvb1
    wa
    #
    @6
    wo
    #
    @7
    @10
    @10
    @13
    @10
    id
    @6
    wvb1
    @0
    @0
    @5
    lea
    mldual2i
    tr
    @12
    @4
    @6
    @0
    wvb1
    ancom
    ror
    tr
    lbtr
    @7
    @4
    @5
    wo
    @8
    @6
    @5
    @4
    @0
    @5
    lear
    lelor
    @4
    @5
    orcom
    lbtr
    letr
end
