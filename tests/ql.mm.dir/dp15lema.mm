include "wo.mm"
include "wa.mm"
include "lor.mm"
include "lan.mm"
include "tr.mm"
include "ran.mm"
include "wt.mm"
include "le1.mm"
include "leran.mm"
include "lelor.mm"
include "an1r.mm"
include "orass.mm"
include "cm.mm"
include "oridm.mm"
include "ror.mm"
include "orcom.mm"
include "3tr.mm"
include "lea.mm"
include "mlduali.mm"
include "lear.mm"
include "leror.mm"
include "bltr.mm"
include "or32.mm"
include "lbtr.mm"
include "letr.mm"

theorem dp15lema
  param wvd: term d
  param wve: term e
  param wva0: term a0
  param wva1: term a1
  param wva2: term a2
  param wvb0: term b0
  param wvb1: term b1
  param wvb2: term b2
  param wvp0: term p0
  assume dp15lema.1: |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) )
  assume dp15lema.2: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume dp15lema.3: |- e = ( b0 ^ ( a0 v p0 ) )


  assert |- ( ( a0 v e ) ^ ( a1 v b1 ) ) =< ( d v b2 )

  proof
    wva0
    wve
    wo
    #
    wva1
    wvb1
    wo
    #
    wa
    wva0
    wvb0
    wva0
    @1
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
    wo
    #
    @1
    wa
    #
    wvd
    wvb2
    wo
    #
    @0
    @6
    @1
    wve
    @5
    wva0
    wve
    wvb0
    wva0
    wvp0
    wo
    #
    wa
    @5
    dp15lema.3
    @9
    @4
    wvb0
    wvp0
    @3
    wva0
    dp15lema.2
    lor
    lan
    tr
    lor
    ran
    @7
    wva0
    wt
    @4
    wa
    #
    wo
    #
    @1
    wa
    #
    @8
    @6
    @11
    @1
    @5
    @10
    wva0
    wvb0
    wt
    @4
    wvb0
    le1
    leran
    lelor
    leran
    @12
    @2
    wva0
    @1
    wa
    #
    wo
    #
    @8
    @12
    @3
    @13
    wo
    #
    @14
    @12
    @3
    wva0
    wo
    #
    @1
    wa
    @15
    @11
    @16
    @1
    @11
    wva0
    @4
    wo
    #
    wva0
    wva0
    wo
    #
    @3
    wo
    #
    @16
    @10
    @4
    wva0
    @4
    an1r
    lor
    @19
    @17
    wva0
    wva0
    @3
    orass
    cm
    @19
    @4
    @16
    @18
    wva0
    @3
    wva0
    oridm
    ror
    wva0
    @3
    orcom
    tr
    3tr
    ran
    @3
    wva0
    @1
    @1
    @2
    lea
    mlduali
    tr
    @3
    @2
    @13
    @1
    @2
    lear
    leror
    bltr
    @14
    wva2
    @13
    wo
    #
    wvb2
    wo
    #
    @8
    wva2
    wvb2
    @13
    or32
    @8
    @21
    wvd
    @20
    wvb2
    dp15lema.1
    ror
    cm
    tr
    lbtr
    letr
    bltr
end
