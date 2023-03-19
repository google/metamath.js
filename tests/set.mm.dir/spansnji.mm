include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cph.mm"
include "cort.mm"
include "chshii.mm"
include "spansnchi.mm"
include "shjshsi.mm"
include "cpjh.mm"
include "cch.mm"
include "cun.mm"
include "chssii.mm"
include "chil.mm"
include "wcel.mm"
include "wss.mm"
include "choccli.mm"
include "pjhclii.mm"
include "snssi.mm"
include "ax-mp.mm"
include "spanuni.mm"
include "csh.mm"
include "wceq.mm"
include "spanid.mm"
include "oveq1i.mm"
include "spansnpji.mm"
include "osumi.mm"
include "3eqtrri.mm"
include "spanunsni.mm"
include "eqtr4i.mm"
include "chjcli.mm"
include "eqeltri.mm"
include "ococi.mm"
include "eqtr2i.mm"

theorem spansnji
  let cA: class A
  let cB: class B
  assume spansnj.1: |- A e. CH
  assume spansnj.2: |- B e. ~H


  assert |- ( A +H ( span ` { B } ) ) = ( A vH ( span ` { B } ) )

  proof
    cA
    cB
    csn
    #
    cspn
    cfv
    #
    chj
    co
    cA
    @1
    cph
    co
    #
    cort
    cfv
    cort
    cfv
    @2
    cA
    @1
    cA
    spansnj.1
    chshii
    #
    @1
    cB
    spansnj.2
    spansnchi
    chshii
    shjshsi
    @2
    @2
    cA
    cB
    cA
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    csn
    #
    cspn
    cfv
    #
    chj
    co
    #
    cch
    @8
    cA
    @0
    cun
    cspn
    cfv
    #
    cA
    cspn
    cfv
    #
    @1
    cph
    co
    @2
    @8
    cA
    @6
    cun
    cspn
    cfv
    #
    @9
    @11
    @10
    @7
    cph
    co
    cA
    @7
    cph
    co
    #
    @8
    cA
    @6
    cA
    spansnj.1
    chssii
    #
    @5
    chil
    wcel
    @6
    chil
    wss
    cB
    @4
    cA
    spansnj.1
    choccli
    spansnj.2
    pjhclii
    #
    @5
    chil
    snssi
    ax-mp
    spanuni
    @10
    cA
    @7
    cph
    cA
    csh
    wcel
    @10
    cA
    wceq
    @3
    cA
    spanid
    ax-mp
    #
    oveq1i
    cA
    @7
    cort
    cfv
    wss
    @12
    @8
    wceq
    cA
    cB
    @13
    spansnj.2
    spansnpji
    cA
    @7
    spansnj.1
    @5
    @14
    spansnchi
    #
    osumi
    ax-mp
    3eqtrri
    cA
    cB
    spansnj.1
    spansnj.2
    spanunsni
    eqtr4i
    cA
    @0
    @13
    cB
    chil
    wcel
    @0
    chil
    wss
    spansnj.2
    cB
    chil
    snssi
    ax-mp
    spanuni
    @10
    cA
    @1
    cph
    @15
    oveq1i
    3eqtrri
    cA
    @7
    spansnj.1
    @16
    chjcli
    eqeltri
    ococi
    eqtr2i
end
