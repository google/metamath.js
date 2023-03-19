include "wo.mm"
include "wa.mm"
include "leo.mm"
include "ml2i.mm"
include "ancom.mm"
include "tr.mm"
include "lor.mm"
include "cm.mm"
include "orass.mm"
include "or12.mm"
include "2an.mm"
include "lerr.mm"
include "3tr.mm"
include "3tr1.mm"

theorem l42modlem1
  let wva: term a
  let wvb: term b
  let wvd: term d
  let wve: term e


  assert |- ( ( ( a v b ) v d ) ^ ( ( a v b ) v e ) ) = ( ( a v b ) v ( ( a v d ) ^ ( b v e ) ) )

  proof
    wva
    wvb
    wve
    wo
    #
    wvb
    wva
    wvd
    wo
    #
    wo
    #
    wa
    #
    wo
    #
    wva
    wvb
    @1
    @0
    wa
    #
    wo
    #
    wo
    #
    wva
    wvb
    wo
    #
    wvd
    wo
    #
    @8
    wve
    wo
    #
    wa
    #
    @8
    @5
    wo
    @7
    @4
    @6
    @3
    wva
    @6
    @2
    @0
    wa
    @3
    @0
    @1
    wvb
    wvb
    wve
    leo
    ml2i
    @2
    @0
    ancom
    tr
    lor
    cm
    @11
    @2
    wva
    @0
    wo
    #
    wa
    @12
    @2
    wa
    #
    @4
    @9
    @2
    @10
    @12
    @9
    wva
    wvb
    wvd
    wo
    wo
    @2
    wva
    wvb
    wvd
    orass
    wva
    wvb
    wvd
    or12
    tr
    wva
    wvb
    wve
    orass
    2an
    @2
    @12
    ancom
    @4
    @13
    @2
    @0
    wva
    wva
    @1
    wvb
    wva
    wvd
    leo
    lerr
    ml2i
    cm
    3tr
    wva
    wvb
    @5
    orass
    3tr1
end
