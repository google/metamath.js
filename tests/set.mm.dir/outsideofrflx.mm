include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cbtwn.mm"
include "wn.mm"
include "wa.mm"
include "coutsideof.mm"
include "wceq.mm"
include "axbtwnid.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "necon3ad.mm"
include "colineartriv2.mm"
include "jctild.mm"
include "broutsideof.mm"
include "syl6ibr.mm"

theorem outsideofrflx
  let cA: class A
  let cP: class P
  let cN: class N


  assert |- ( ( N e. NN /\ P e. ( EE ` N ) /\ A e. ( EE ` N ) ) -> ( A =/= P -> P OutsideOf <. A , A >. ) )

  proof
    cN
    cn
    wcel
    cP
    cN
    cee
    cfv
    #
    wcel
    cA
    @0
    wcel
    w3a
    #
    cA
    cP
    wne
    #
    cP
    cA
    cA
    cop
    #
    ccolin
    wbr
    #
    cP
    @3
    cbtwn
    wbr
    #
    wn
    #
    wa
    cP
    @3
    coutsideof
    wbr
    @1
    @2
    @6
    @4
    @1
    @5
    cA
    cP
    @1
    @5
    cP
    cA
    wceq
    cA
    cP
    wceq
    cP
    cA
    cN
    axbtwnid
    cP
    cA
    eqcom
    syl6ib
    necon3ad
    cP
    cA
    cN
    colineartriv2
    jctild
    cA
    cA
    cP
    broutsideof
    syl6ibr
end
