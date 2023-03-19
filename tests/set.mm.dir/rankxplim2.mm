include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "crnk.mm"
include "cfv.mm"
include "wlim.mm"
include "cun.mm"
include "wceq.mm"
include "wn.mm"
include "wcel.mm"
include "0ellim.mm"
include "n0i.mm"
include "syl.mm"
include "df-ne.mm"
include "xpex.mm"
include "rankeq0.mm"
include "notbii.mm"
include "bitr2i.mm"
include "sylib.mm"
include "cuni.mm"
include "limuni2.mm"
include "wb.mm"
include "rankuni.mm"
include "unieqi.mm"
include "eqtr2i.mm"
include "unixp.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "limeq.mm"
include "syl5ib.mm"
include "mpcom.mm"

theorem rankxplim2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rankxplim.1: |- A e. _V
  assume rankxplim.2: |- B e. _V


  assert |- ( Lim ( rank ` ( A X. B ) ) -> Lim ( rank ` ( A u. B ) ) )

  proof
    cA
    cB
    cxp
    #
    c0
    wne
    #
    @0
    crnk
    cfv
    #
    wlim
    #
    cA
    cB
    cun
    #
    crnk
    cfv
    #
    wlim
    #
    @3
    @2
    c0
    wceq
    #
    wn
    #
    @1
    @3
    c0
    @2
    wcel
    @8
    @2
    0ellim
    @2
    c0
    n0i
    syl
    @1
    @0
    c0
    wceq
    #
    wn
    @8
    @0
    c0
    df-ne
    @9
    @7
    @0
    cA
    cB
    rankxplim.1
    rankxplim.2
    xpex
    rankeq0
    notbii
    bitr2i
    sylib
    @3
    @2
    cuni
    #
    cuni
    #
    wlim
    #
    @1
    @6
    @3
    @10
    wlim
    @12
    @2
    limuni2
    @10
    limuni2
    syl
    @1
    @11
    @5
    wceq
    @12
    @6
    wb
    @1
    @11
    @0
    cuni
    #
    cuni
    #
    crnk
    cfv
    #
    @5
    @15
    @13
    crnk
    cfv
    #
    cuni
    @11
    @13
    rankuni
    @16
    @10
    @0
    rankuni
    unieqi
    eqtr2i
    @1
    @14
    @4
    crnk
    cA
    cB
    unixp
    fveq2d
    syl5eq
    @11
    @5
    limeq
    syl
    syl5ib
    mpcom
end
