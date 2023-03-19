include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "pjhcli.mm"
include "pjadji.mm"
include "sylan.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "pjcoi.mm"
include "oveq1d.mm"
include "adantr.mm"
include "oveq2d.mm"
include "adantl.mm"
include "3eqtr4d.mm"

theorem pjadjcoi
  let cA: class A
  let cB: class B
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( ( ( projh ` G ) o. ( projh ` H ) ) ` A ) .ih B ) = ( A .ih ( ( ( projh ` H ) o. ( projh ` G ) ) ` B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cG
    cpjh
    cfv
    #
    cfv
    #
    cB
    csp
    co
    #
    cA
    cB
    @5
    cfv
    #
    @3
    cfv
    #
    csp
    co
    #
    cA
    @5
    @3
    ccom
    cfv
    #
    cB
    csp
    co
    #
    cA
    cB
    @3
    @5
    ccom
    cfv
    #
    csp
    co
    #
    @2
    @7
    @4
    @8
    csp
    co
    #
    @10
    @0
    @4
    chil
    wcel
    @1
    @7
    @15
    wceq
    cA
    cH
    pjco.2
    pjhcli
    @4
    cB
    cG
    pjco.1
    pjadji
    sylan
    @1
    @0
    @8
    chil
    wcel
    @15
    @10
    wceq
    cB
    cG
    pjco.1
    pjhcli
    cA
    @8
    cH
    pjco.2
    pjadji
    sylan2
    eqtrd
    @0
    @12
    @7
    wceq
    @1
    @0
    @11
    @6
    cB
    csp
    cA
    cG
    cH
    pjco.1
    pjco.2
    pjcoi
    oveq1d
    adantr
    @1
    @14
    @10
    wceq
    @0
    @1
    @13
    @9
    cA
    csp
    cB
    cH
    cG
    pjco.2
    pjco.1
    pjcoi
    oveq2d
    adantl
    3eqtr4d
end
