include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "wss.mm"
include "wceq.mm"
include "csdm.mm"
include "wpss.mm"
include "nndomo.mm"
include "nneneq.mm"
include "notbid.mm"
include "anbi12d.mm"
include "brsdom.mm"
include "dfpss2.mm"
include "3bitr4g.mm"

theorem nnsdomo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A ~< B <-> A C. B ) )

  proof
    cA
    com
    wcel
    cB
    com
    wcel
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wn
    #
    wa
    cA
    cB
    wss
    #
    cA
    cB
    wceq
    #
    wn
    #
    wa
    cA
    cB
    csdm
    wbr
    cA
    cB
    wpss
    @0
    @1
    @4
    @3
    @6
    cA
    cB
    nndomo
    @0
    @2
    @5
    cA
    cB
    nneneq
    notbid
    anbi12d
    cA
    cB
    brsdom
    cA
    cB
    dfpss2
    3bitr4g
end
