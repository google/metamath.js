include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "ccxp.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "cxplt.mm"
include "ancom2s.mm"
include "notbid.mm"
include "lenlt.mm"
include "adantl.mm"
include "cc0.mm"
include "simpll.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "simplr.mm"
include "lttrd.mm"
include "ltled.mm"
include "simprl.mm"
include "recxpcl.mm"
include "syl3anc.mm"
include "simprr.mm"
include "lenltd.mm"
include "3bitr4d.mm"

theorem cxple
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 1 < A ) /\ ( B e. RR /\ C e. RR ) ) -> ( B <_ C <-> ( A ^c B ) <_ ( A ^c C ) ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    wa
    #
    wa
    #
    cC
    cB
    clt
    wbr
    #
    wn
    #
    cA
    cC
    ccxp
    co
    #
    cA
    cB
    ccxp
    co
    #
    clt
    wbr
    #
    wn
    cB
    cC
    cle
    wbr
    #
    @10
    @9
    cle
    wbr
    @6
    @7
    @11
    @2
    @4
    @3
    @7
    @11
    wb
    cA
    cC
    cB
    cxplt
    ancom2s
    notbid
    @5
    @12
    @8
    wb
    @2
    cB
    cC
    lenlt
    adantl
    @6
    @10
    @9
    @6
    @0
    cc0
    cA
    cle
    wbr
    #
    @3
    @10
    cr
    wcel
    @0
    @1
    @5
    simpll
    #
    @6
    cc0
    cA
    @6
    0red
    #
    @14
    @6
    cc0
    c1
    cA
    @15
    @6
    1red
    @14
    cc0
    c1
    clt
    wbr
    @6
    0lt1
    a1i
    @0
    @1
    @5
    simplr
    lttrd
    ltled
    #
    @2
    @3
    @4
    simprl
    cA
    cB
    recxpcl
    syl3anc
    @6
    @0
    @13
    @4
    @9
    cr
    wcel
    @14
    @16
    @2
    @3
    @4
    simprr
    cA
    cC
    recxpcl
    syl3anc
    lenltd
    3bitr4d
end
