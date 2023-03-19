include "wo.mm"
include "wa.mm"
include "lea.mm"
include "dp35leme.mm"
include "ler2an.mm"
include "mldual2i.mm"
include "lel2or.mm"
include "ancom.mm"
include "bile.mm"
include "lear.mm"
include "le2or.mm"
include "orass.mm"
include "cm.mm"
include "lbtr.mm"
include "bltr.mm"
include "letr.mm"

theorem dp35lemd
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


  assert |- ( b0 ^ ( a0 v p0 ) ) =< ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) )

  proof
    wvb0
    wva0
    wvp0
    wo
    #
    wa
    #
    wvb0
    wva0
    wvb0
    wvb1
    wvc2
    wvc0
    wvc1
    wo
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wvb0
    wva0
    wvb0
    wa
    #
    wvb1
    wo
    @2
    wo
    #
    wa
    #
    @1
    wvb0
    @5
    wvb0
    @0
    lea
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
    dp35leme
    ler2an
    @6
    wvb0
    wva0
    wa
    #
    @4
    wo
    #
    @9
    @4
    wva0
    wvb0
    wvb0
    @3
    lea
    #
    mldual2i
    @11
    wvb0
    @8
    @10
    wvb0
    @4
    wvb0
    wva0
    lea
    @12
    lel2or
    @11
    @7
    @3
    wo
    #
    @8
    @10
    @7
    @4
    @3
    @10
    @7
    wvb0
    wva0
    ancom
    bile
    wvb0
    @3
    lear
    le2or
    @8
    @13
    @7
    wvb1
    @2
    orass
    cm
    lbtr
    ler2an
    bltr
    letr
end
