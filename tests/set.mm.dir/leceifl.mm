include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cneg.mm"
include "cle.mm"
include "wb.mm"
include "ltflcei.mm"
include "ancoms.mm"
include "notbid.mm"
include "reflcl.mm"
include "lenlt.mm"
include "sylan2.mm"
include "ceicl.mm"
include "zred.mm"
include "sylan.mm"
include "3bitr4rd.mm"

theorem leceifl
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( -u ( |_ ` -u A ) <_ B <-> A <_ ( |_ ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cB
    cfl
    cfv
    #
    cA
    clt
    wbr
    #
    wn
    #
    cB
    cA
    cneg
    cfl
    cfv
    cneg
    #
    clt
    wbr
    #
    wn
    #
    cA
    @3
    cle
    wbr
    #
    @6
    cB
    cle
    wbr
    #
    @2
    @4
    @7
    @1
    @0
    @4
    @7
    wb
    cB
    cA
    ltflcei
    ancoms
    notbid
    @1
    @0
    @3
    cr
    wcel
    @9
    @5
    wb
    cB
    reflcl
    cA
    @3
    lenlt
    sylan2
    @0
    @6
    cr
    wcel
    @1
    @10
    @8
    wb
    @0
    @6
    cA
    ceicl
    zred
    @6
    cB
    lenlt
    sylan
    3bitr4rd
end
