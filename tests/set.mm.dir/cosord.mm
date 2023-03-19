include "cc0.mm"
include "cpi.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "ccos.mm"
include "cfv.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "cosordlem.mm"
include "ex.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "a1i.mm"
include "orim12d.mm"
include "con3d.mm"
include "cr.mm"
include "wb.mm"
include "cle.mm"
include "0re.mm"
include "pire.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "recoscl.mm"
include "axlttri.mm"
include "syl2anr.mm"
include "syl2an.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem cosord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,] _pi ) /\ B e. ( 0 [,] _pi ) ) -> ( A < B <-> ( cos ` B ) < ( cos ` A ) ) )

  proof
    cA
    cc0
    cpi
    cicc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cB
    ccos
    cfv
    #
    cA
    ccos
    cfv
    #
    clt
    wbr
    #
    @3
    @4
    @7
    @3
    @4
    wa
    cA
    cB
    @1
    @2
    @4
    simpll
    @1
    @2
    @4
    simplr
    @3
    @4
    simpr
    cosordlem
    ex
    @3
    @5
    @6
    wceq
    #
    @6
    @5
    clt
    wbr
    #
    wo
    #
    wn
    #
    cA
    cB
    wceq
    #
    cB
    cA
    clt
    wbr
    #
    wo
    #
    wn
    #
    @7
    @4
    @3
    @14
    @10
    @3
    @12
    @8
    @13
    @9
    @12
    @8
    wi
    @3
    @12
    @6
    @5
    cA
    cB
    ccos
    fveq2
    eqcomd
    a1i
    @3
    @13
    @9
    @3
    @13
    wa
    cB
    cA
    @1
    @2
    @13
    simplr
    @1
    @2
    @13
    simpll
    @3
    @13
    simpr
    cosordlem
    ex
    orim12d
    con3d
    @1
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @7
    @11
    wb
    #
    @2
    @1
    @16
    cc0
    cA
    cle
    wbr
    cA
    cpi
    cle
    wbr
    cc0
    cpi
    cA
    0re
    pire
    elicc2i
    simp1bi
    #
    @2
    @17
    cc0
    cB
    cle
    wbr
    cB
    cpi
    cle
    wbr
    cc0
    cpi
    cB
    0re
    pire
    elicc2i
    simp1bi
    #
    @17
    @5
    cr
    wcel
    @6
    cr
    wcel
    @18
    @16
    cB
    recoscl
    cA
    recoscl
    @5
    @6
    axlttri
    syl2anr
    syl2an
    @1
    @16
    @17
    @4
    @15
    wb
    @2
    @19
    @20
    cA
    cB
    axlttri
    syl2an
    3imtr4d
    impbid
end
