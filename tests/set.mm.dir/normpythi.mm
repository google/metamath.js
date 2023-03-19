include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cva.mm"
include "caddc.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "normlem8.mm"
include "id.mm"
include "chil.mm"
include "wcel.mm"
include "wb.mm"
include "orthcom.mm"
include "mp2an.mm"
include "biimpi.mm"
include "oveq12d.mm"
include "00id.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "hicli.mm"
include "addcli.mm"
include "addid1i.mm"
include "syl5eq.mm"
include "hvaddcli.mm"
include "normsqi.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"

theorem normpythi
  let cA: class A
  let cB: class B
  assume normsub.1: |- A e. ~H
  assume normsub.2: |- B e. ~H


  assert |- ( ( A .ih B ) = 0 -> ( ( normh ` ( A +h B ) ) ^ 2 ) = ( ( ( normh ` A ) ^ 2 ) + ( ( normh ` B ) ^ 2 ) ) )

  proof
    cA
    cB
    csp
    co
    #
    cc0
    wceq
    #
    cA
    cB
    cva
    co
    #
    @2
    csp
    co
    #
    cA
    cA
    csp
    co
    #
    cB
    cB
    csp
    co
    #
    caddc
    co
    #
    @2
    cno
    cfv
    c2
    cexp
    co
    cA
    cno
    cfv
    c2
    cexp
    co
    #
    cB
    cno
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    @1
    @3
    @6
    @0
    cB
    cA
    csp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @6
    cA
    cB
    cA
    cB
    normsub.1
    normsub.2
    normsub.1
    normsub.2
    normlem8
    @1
    @11
    @6
    cc0
    caddc
    co
    @6
    @1
    @10
    cc0
    @6
    caddc
    @1
    @10
    cc0
    cc0
    caddc
    co
    cc0
    @1
    @0
    cc0
    @9
    cc0
    caddc
    @1
    id
    @1
    @9
    cc0
    wceq
    #
    cA
    chil
    wcel
    cB
    chil
    wcel
    @1
    @12
    wb
    normsub.1
    normsub.2
    cA
    cB
    orthcom
    mp2an
    biimpi
    oveq12d
    00id
    syl6eq
    oveq2d
    @6
    @4
    @5
    cA
    cA
    normsub.1
    normsub.1
    hicli
    cB
    cB
    normsub.2
    normsub.2
    hicli
    addcli
    addid1i
    syl6eq
    syl5eq
    @2
    cA
    cB
    normsub.1
    normsub.2
    hvaddcli
    normsqi
    @7
    @4
    @8
    @5
    caddc
    cA
    normsub.1
    normsqi
    cB
    normsub.2
    normsqi
    oveq12i
    3eqtr4g
end
