include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ax-a1.mm"
include "lor.mm"
include "lan.mm"
include "orcom.mm"
include "ran.mm"
include "2an.mm"
include "2or.mm"
include "tr.mm"
include "3tr2.mm"
include "k1-4.mm"

theorem k1-5
  param wvc: term c
  param wvx: term x
  assume k1-5.1: |- ( x ' ^ ( x v c ) ) = ( ( ( x ' ^ ( x v c ) ) ^ c ) v ( ( x ' ^ ( x v c ) ) ^ c ' ) )
  assume k1-5.2: |- x =< c '


  assert |- ( x v ( x ' ^ c ' ) ) = c '

  proof
    wvc
    wn
    #
    wvx
    wvx
    wn
    #
    wvx
    wvc
    wo
    #
    wa
    #
    @3
    wvc
    wa
    #
    @3
    @0
    wa
    #
    wo
    #
    @1
    wvx
    @0
    wn
    #
    wo
    #
    wa
    #
    @9
    @0
    wa
    #
    @9
    @7
    wa
    #
    wo
    #
    k1-5.1
    @2
    @8
    @1
    wvc
    @7
    wvx
    wvc
    ax-a1
    #
    lor
    lan
    #
    @6
    @5
    @4
    wo
    @12
    @4
    @5
    orcom
    @5
    @10
    @4
    @11
    @3
    @9
    @0
    @14
    ran
    @3
    @9
    wvc
    @7
    @14
    @13
    2an
    2or
    tr
    3tr2
    k1-5.2
    k1-4
end
