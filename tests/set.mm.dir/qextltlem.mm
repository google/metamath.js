include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "cq.mm"
include "wrex.mm"
include "wb.mm"
include "wn.mm"
include "cle.mm"
include "qbtwnxr.mm"
include "3expia.mm"
include "simprl.mm"
include "simplll.mm"
include "qre.mm"
include "rexrd.mm"
include "ad2antlr.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wi.mm"
include "xrltle.mm"
include "mtod.mm"
include "simprr.mm"
include "2thd.mm"
include "nbbn.mm"
include "sylib.mm"
include "simpllr.mm"
include "mpd.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "syld.mm"

theorem qextltlem
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B -> E. x e. QQ ( -. ( x < A <-> x < B ) /\ -. ( x <_ A <-> x <_ B ) ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    vx
    cv
    #
    clt
    wbr
    #
    @4
    cB
    clt
    wbr
    #
    wa
    #
    vx
    cq
    wrex
    #
    @4
    cA
    clt
    wbr
    #
    @6
    wb
    wn
    #
    @4
    cA
    cle
    wbr
    #
    @4
    cB
    cle
    wbr
    #
    wb
    wn
    #
    wa
    #
    vx
    cq
    wrex
    @0
    @1
    @3
    @8
    vx
    cA
    cB
    qbtwnxr
    3expia
    @2
    @7
    @14
    vx
    cq
    @2
    @4
    cq
    wcel
    #
    wa
    #
    @7
    @14
    @16
    @7
    wa
    #
    @10
    @13
    @17
    @9
    wn
    #
    @6
    wb
    @10
    @17
    @18
    @6
    @17
    @9
    @11
    @17
    @5
    @11
    wn
    #
    @16
    @5
    @6
    simprl
    @17
    @0
    @4
    cxr
    wcel
    #
    @5
    @19
    wb
    @0
    @1
    @15
    @7
    simplll
    #
    @15
    @20
    @2
    @7
    @15
    @4
    @4
    qre
    rexrd
    ad2antlr
    #
    cA
    @4
    xrltnle
    syl2anc
    mpbid
    #
    @17
    @20
    @0
    @9
    @11
    wi
    @22
    @21
    @4
    cA
    xrltle
    syl2anc
    mtod
    @16
    @5
    @6
    simprr
    #
    2thd
    @9
    @6
    nbbn
    sylib
    @17
    @19
    @12
    wb
    @13
    @17
    @19
    @12
    @23
    @17
    @6
    @12
    @24
    @17
    @20
    @1
    @6
    @12
    wi
    @22
    @0
    @1
    @15
    @7
    simpllr
    @4
    cB
    xrltle
    syl2anc
    mpd
    2thd
    @11
    @12
    nbbn
    sylib
    jca
    ex
    reximdva
    syld
end
