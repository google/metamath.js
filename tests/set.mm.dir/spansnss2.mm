include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "spansnss.mm"
include "ex.mm"
include "adantr.mm"
include "spansnid.mm"
include "ssel.mm"
include "syl5com.mm"
include "adantl.mm"
include "impbid.mm"

theorem spansnss2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. SH /\ B e. ~H ) -> ( B e. A <-> ( span ` { B } ) C_ A ) )

  proof
    cA
    csh
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    cB
    cA
    wcel
    #
    cB
    csn
    cspn
    cfv
    #
    cA
    wss
    #
    @0
    @2
    @4
    wi
    @1
    @0
    @2
    @4
    cA
    cB
    spansnss
    ex
    adantr
    @1
    @4
    @2
    wi
    @0
    @1
    cB
    @3
    wcel
    @4
    @2
    cB
    spansnid
    @3
    cA
    cB
    ssel
    syl5com
    adantl
    impbid
end
