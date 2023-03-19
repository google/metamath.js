include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wb.mm"
include "cneg.mm"
include "wi.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "eqeq1d.mm"
include "a1i.mm"
include "negmod0.mm"
include "bibi2d.mm"
include "syl5ibrcom.mm"
include "wo.mm"
include "absor.mm"
include "adantr.mm"
include "mpjaod.mm"

theorem absmod0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A mod B ) = 0 <-> ( ( abs ` A ) mod B ) = 0 ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cabs
    cfv
    #
    cA
    wceq
    #
    cA
    cB
    cmo
    co
    #
    cc0
    wceq
    #
    @3
    cB
    cmo
    co
    #
    cc0
    wceq
    #
    wb
    #
    @3
    cA
    cneg
    #
    wceq
    #
    @4
    @9
    wi
    @2
    @4
    @5
    @7
    cc0
    @5
    @7
    wceq
    cA
    @3
    cA
    @3
    cB
    cmo
    oveq1
    eqcoms
    eqeq1d
    a1i
    @2
    @9
    @11
    @6
    @10
    cB
    cmo
    co
    #
    cc0
    wceq
    #
    wb
    cA
    cB
    negmod0
    @11
    @8
    @13
    @6
    @11
    @7
    @12
    cc0
    @3
    @10
    cB
    cmo
    oveq1
    eqeq1d
    bibi2d
    syl5ibrcom
    @0
    @4
    @11
    wo
    @1
    cA
    absor
    adantr
    mpjaod
end
