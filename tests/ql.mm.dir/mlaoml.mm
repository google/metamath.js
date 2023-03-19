include "wi1.mm"
include "wa.mm"
include "tb.mm"
include "u1lembi.mm"
include "ran.mm"
include "mlalem.mm"
include "bltr.mm"
include "ancom.mm"
include "an32.mm"
include "3tr.mm"
include "le2an.mm"
include "an12.mm"
include "id.mm"
include "anandi.mm"
include "3tr1.mm"
include "anass.mm"
include "anandir.mm"
include "3tr2.mm"
include "2an.mm"
include "le3tr2.mm"

theorem mlaoml
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a == b ) ^ ( b == c ) ) =< ( a == c )

  proof
    wva
    wvb
    wi1
    #
    wvb
    wva
    wi1
    #
    wa
    #
    wvb
    wvc
    wi1
    #
    wa
    #
    @1
    wvc
    wvb
    wi1
    #
    wa
    #
    @3
    wa
    #
    wa
    #
    wva
    wvc
    wi1
    #
    wvc
    wva
    wi1
    #
    wa
    wva
    wvb
    tb
    #
    wvb
    wvc
    tb
    #
    wa
    #
    wva
    wvc
    tb
    @4
    @9
    @7
    @10
    @4
    @11
    @3
    wa
    @9
    @2
    @11
    @3
    wva
    wvb
    u1lembi
    #
    ran
    wva
    wvb
    wvc
    mlalem
    bltr
    @7
    wvc
    wvb
    tb
    #
    @1
    wa
    #
    @10
    @7
    @5
    @1
    wa
    #
    @3
    wa
    @5
    @3
    wa
    #
    @1
    wa
    @16
    @6
    @17
    @3
    @1
    @5
    ancom
    ran
    @5
    @1
    @3
    an32
    @18
    @15
    @1
    wvc
    wvb
    u1lembi
    ran
    3tr
    wvc
    wvb
    wva
    mlalem
    bltr
    le2an
    @8
    @4
    @5
    wa
    #
    @2
    @3
    @5
    wa
    #
    wa
    @13
    @2
    @6
    wa
    #
    @3
    wa
    @2
    @5
    wa
    #
    @3
    wa
    @8
    @19
    @21
    @22
    @3
    @1
    @0
    @5
    wa
    wa
    #
    @0
    @6
    wa
    @21
    @22
    @1
    @0
    @5
    an12
    @21
    @1
    @0
    wa
    #
    @6
    wa
    @21
    @23
    @2
    @24
    @6
    @0
    @1
    ancom
    ran
    @21
    id
    @1
    @0
    @5
    anandi
    3tr1
    @0
    @1
    @5
    anass
    3tr1
    ran
    @2
    @6
    @3
    anandir
    @2
    @5
    @3
    an32
    3tr2
    @2
    @3
    @5
    anass
    @2
    @11
    @20
    @12
    @14
    wvb
    wvc
    u1lembi
    2an
    3tr
    wva
    wvc
    u1lembi
    le3tr2
end
