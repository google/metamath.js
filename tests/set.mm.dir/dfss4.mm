include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "cdif.mm"
include "sseqin2.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "notbii.mm"
include "anbi2i.mm"
include "wi.mm"
include "elin.mm"
include "abai.mm"
include "iman.mm"
include "3bitri.mm"
include "bitr4i.mm"
include "difeqri.mm"
include "eqeq1i.mm"

theorem dfss4
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ B <-> ( B \ ( B \ A ) ) = A )

  proof
    cA
    cB
    wss
    cB
    cA
    cin
    #
    cA
    wceq
    cB
    cB
    cA
    cdif
    #
    cdif
    #
    cA
    wceq
    cA
    cB
    sseqin2
    @2
    @0
    cA
    vx
    cB
    @1
    @0
    vx
    cv
    #
    cB
    wcel
    #
    @3
    @1
    wcel
    #
    wn
    #
    wa
    @4
    @4
    @3
    cA
    wcel
    #
    wn
    wa
    #
    wn
    #
    wa
    #
    @3
    @0
    wcel
    #
    @6
    @9
    @4
    @5
    @8
    @3
    cB
    cA
    eldif
    notbii
    anbi2i
    @11
    @4
    @7
    wa
    @4
    @4
    @7
    wi
    #
    wa
    @10
    @3
    cB
    cA
    elin
    @4
    @7
    abai
    @12
    @9
    @4
    @4
    @7
    iman
    anbi2i
    3bitri
    bitr4i
    difeqri
    eqeq1i
    bitr4i
end
