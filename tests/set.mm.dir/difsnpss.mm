include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "wpss.mm"
include "notnotb.mm"
include "wne.mm"
include "wss.mm"
include "wa.mm"
include "difss.mm"
include "biantrur.mm"
include "difsnb.mm"
include "necon3bbii.mm"
include "df-pss.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem difsnpss
  let cA: class A
  let cB: class B


  assert |- ( A e. B <-> ( B \ { A } ) C. B )

  proof
    cA
    cB
    wcel
    #
    @0
    wn
    #
    wn
    #
    cB
    cA
    csn
    #
    cdif
    #
    cB
    wpss
    #
    @0
    notnotb
    @4
    cB
    wne
    #
    @4
    cB
    wss
    #
    @6
    wa
    @2
    @5
    @7
    @6
    cB
    @3
    difss
    biantrur
    @1
    @4
    cB
    cA
    cB
    difsnb
    necon3bbii
    @4
    cB
    df-pss
    3bitr4i
    bitri
end
