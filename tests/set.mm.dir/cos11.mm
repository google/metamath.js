include "cc0.mm"
include "cpi.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "ccos.mm"
include "cfv.mm"
include "wceq.mm"
include "ancom.mm"
include "wb.mm"
include "cosord.mm"
include "ancoms.mm"
include "notbid.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "cr.mm"
include "cle.mm"
include "0re.mm"
include "pire.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "lttri3.mm"
include "syl2an.mm"
include "recoscl.mm"
include "3bitr4d.mm"

theorem cos11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,] _pi ) /\ B e. ( 0 [,] _pi ) ) -> ( A = B <-> ( cos ` A ) = ( cos ` B ) ) )

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
    wn
    #
    cB
    cA
    clt
    wbr
    #
    wn
    #
    wa
    #
    cA
    ccos
    cfv
    #
    cB
    ccos
    cfv
    #
    clt
    wbr
    #
    wn
    #
    @10
    @9
    clt
    wbr
    #
    wn
    #
    wa
    #
    cA
    cB
    wceq
    #
    @9
    @10
    wceq
    #
    @8
    @7
    @5
    wa
    @3
    @15
    @5
    @7
    ancom
    @3
    @7
    @12
    @5
    @14
    @3
    @6
    @11
    @2
    @1
    @6
    @11
    wb
    cB
    cA
    cosord
    ancoms
    notbid
    @3
    @4
    @13
    cA
    cB
    cosord
    notbid
    anbi12d
    syl5bb
    @1
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @16
    @8
    wb
    @2
    @1
    @18
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
    @19
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
    cA
    cB
    lttri3
    syl2an
    @1
    @18
    @19
    @17
    @15
    wb
    #
    @2
    @20
    @21
    @18
    @9
    cr
    wcel
    @10
    cr
    wcel
    @22
    @19
    cA
    recoscl
    cB
    recoscl
    @9
    @10
    lttri3
    syl2an
    syl2an
    3bitr4d
end
