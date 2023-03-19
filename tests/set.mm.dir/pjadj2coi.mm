include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "pjhcli.mm"
include "pjadjcoi.mm"
include "sylan.mm"
include "pjcohcli.mm"
include "pjadji.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "pjfi.mm"
include "hocofi.mm"
include "hocoi.mm"
include "oveq1d.mm"
include "adantr.mm"
include "coass.mm"
include "fveq1i.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "adantl.mm"
include "3eqtr4d.mm"

theorem pjadj2coi
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjadj2co.1: |- F e. CH
  assume pjadj2co.2: |- G e. CH
  assume pjadj2co.3: |- H e. CH


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) ` A ) .ih B ) = ( A .ih ( ( ( ( projh ` H ) o. ( projh ` G ) ) o. ( projh ` F ) ) ` B ) ) )

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
    cF
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    #
    cfv
    #
    cB
    csp
    co
    #
    cA
    cB
    @6
    @5
    ccom
    #
    cfv
    #
    @3
    cfv
    #
    csp
    co
    #
    cA
    @7
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
    @6
    ccom
    @5
    ccom
    #
    cfv
    #
    csp
    co
    #
    @2
    @9
    @4
    @11
    csp
    co
    #
    @13
    @0
    @4
    chil
    wcel
    @1
    @9
    @19
    wceq
    cA
    cH
    pjadj2co.3
    pjhcli
    @4
    cB
    cF
    cG
    pjadj2co.1
    pjadj2co.2
    pjadjcoi
    sylan
    @1
    @0
    @11
    chil
    wcel
    @19
    @13
    wceq
    cB
    cG
    cF
    pjadj2co.2
    pjadj2co.1
    pjcohcli
    cA
    @11
    cH
    pjadj2co.3
    pjadji
    sylan2
    eqtrd
    @0
    @15
    @9
    wceq
    @1
    @0
    @14
    @8
    cB
    csp
    cA
    @7
    @3
    @5
    @6
    cF
    pjadj2co.1
    pjfi
    #
    cG
    pjadj2co.2
    pjfi
    #
    hocofi
    cH
    pjadj2co.3
    pjfi
    #
    hocoi
    oveq1d
    adantr
    @1
    @18
    @13
    wceq
    @0
    @1
    @17
    @12
    cA
    csp
    @1
    @17
    cB
    @3
    @10
    ccom
    #
    cfv
    @12
    cB
    @16
    @23
    @3
    @6
    @5
    coass
    fveq1i
    cB
    @3
    @10
    @22
    @6
    @5
    @21
    @20
    hocofi
    hocoi
    syl5eq
    oveq2d
    adantl
    3eqtr4d
end
