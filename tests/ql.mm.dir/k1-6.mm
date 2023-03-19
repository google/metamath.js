include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anor3.mm"
include "cm.mm"
include "con4.mm"
include "oran3.mm"
include "oran2.mm"
include "2an.mm"
include "3tr1.mm"
include "ran.mm"
include "anass.mm"
include "ancom.mm"
include "ax-a2.mm"
include "lan.mm"
include "anabs.mm"
include "3tr.mm"

theorem k1-6
  let wvc: term c
  let wvx: term x
  assume k1-6.1: |- x = ( ( x ^ c ) v ( x ^ c ' ) )


  assert |- ( x ' ^ c ) = ( ( x ' v c ' ) ^ c )

  proof
    wvx
    wn
    #
    wvc
    wa
    @0
    wvc
    wn
    #
    wo
    #
    @0
    wvc
    wo
    #
    wa
    #
    wvc
    wa
    @2
    @3
    wvc
    wa
    #
    wa
    @2
    wvc
    wa
    @0
    @4
    wvc
    wvx
    wvc
    wa
    #
    wvx
    @1
    wa
    #
    wo
    #
    wn
    #
    @6
    wn
    #
    @7
    wn
    #
    wa
    #
    @0
    @4
    @12
    @9
    @6
    @7
    anor3
    cm
    wvx
    @8
    k1-6.1
    con4
    @2
    @10
    @3
    @11
    wvx
    wvc
    oran3
    wvx
    wvc
    oran2
    2an
    3tr1
    ran
    @2
    @3
    wvc
    anass
    @5
    wvc
    @2
    @5
    wvc
    @3
    wa
    wvc
    wvc
    @0
    wo
    #
    wa
    wvc
    @3
    wvc
    ancom
    @3
    @13
    wvc
    @0
    wvc
    ax-a2
    lan
    wvc
    @0
    anabs
    3tr
    lan
    3tr
end
