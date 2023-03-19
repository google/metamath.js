include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "wceq.mm"
include "wcel.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "onint.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "wi.mm"
include "eleq2.mm"
include "biimpd.mm"
include "onnmin.mm"
include "ex.mm"
include "con2d.mm"
include "syl9r.mm"
include "ralrimdv.mm"
include "adantr.mm"
include "jcad.mm"
include "oneqmini.mm"
include "impbid.mm"

theorem oneqmin
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( B C_ On /\ B =/= (/) ) -> ( A = |^| B <-> ( A e. B /\ A. x e. A -. x e. B ) ) )

  proof
    cB
    con0
    wss
    #
    cB
    c0
    wne
    #
    wa
    #
    cA
    cB
    cint
    #
    wceq
    #
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    wn
    #
    vx
    cA
    wral
    #
    wa
    #
    @2
    @4
    @5
    @9
    @2
    @5
    @4
    @3
    cB
    wcel
    cB
    onint
    cA
    @3
    cB
    eleq1
    syl5ibrcom
    @0
    @4
    @9
    wi
    @1
    @0
    @4
    @8
    vx
    cA
    @4
    @6
    cA
    wcel
    #
    @6
    @3
    wcel
    #
    @0
    @8
    @4
    @11
    @12
    cA
    @3
    @6
    eleq2
    biimpd
    @0
    @7
    @12
    @0
    @7
    @12
    wn
    cB
    @6
    onnmin
    ex
    con2d
    syl9r
    ralrimdv
    adantr
    jcad
    @0
    @10
    @4
    wi
    @1
    vx
    cA
    cB
    oneqmini
    adantr
    impbid
end
