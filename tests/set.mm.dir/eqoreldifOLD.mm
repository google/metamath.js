include "wcel.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "orc.mm"
include "a1d.mm"
include "wn.mm"
include "simprr.mm"
include "elsni.mm"
include "a1i.mm"
include "con3d.mm"
include "impcom.mm"
include "eldifd.mm"
include "olcd.mm"
include "ex.mm"
include "pm2.61i.mm"
include "eleq1.mm"
include "biimprd.mm"
include "eldifi.mm"
include "jaoi.mm"
include "com12.mm"
include "impbid.mm"

theorem eqoreldifOLD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B e. C -> ( A e. C <-> ( A = B \/ A e. ( C \ { B } ) ) ) )

  proof
    cB
    cC
    wcel
    #
    cA
    cC
    wcel
    #
    cA
    cB
    wceq
    #
    cA
    cC
    cB
    csn
    #
    cdif
    wcel
    #
    wo
    #
    @0
    @1
    @5
    @2
    @0
    @1
    wa
    #
    @5
    wi
    @2
    @5
    @6
    @2
    @4
    orc
    a1d
    @2
    wn
    #
    @6
    @5
    @7
    @6
    wa
    #
    @4
    @2
    @8
    cA
    cC
    @3
    @7
    @0
    @1
    simprr
    @6
    @7
    cA
    @3
    wcel
    #
    wn
    @6
    @9
    @2
    @9
    @2
    wi
    @6
    cA
    cB
    elsni
    a1i
    con3d
    impcom
    eldifd
    olcd
    ex
    pm2.61i
    ex
    @5
    @0
    @1
    @2
    @0
    @1
    wi
    @4
    @2
    @1
    @0
    cA
    cB
    cC
    eleq1
    biimprd
    @4
    @1
    @0
    cA
    cC
    @3
    eldifi
    a1d
    jaoi
    com12
    impbid
end
