include "csp.mm"
include "co.mm"
include "cva.mm"
include "cmv.mm"
include "cmin.mm"
include "ci.mm"
include "csm.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "polid2i.mm"
include "hvaddcli.mm"
include "normsqi.mm"
include "hvsubcli.mm"
include "oveq12i.mm"
include "ax-icn.mm"
include "hvmulcli.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "eqtr4i.mm"

theorem polidi
  let cA: class A
  let cB: class B
  assume polid.1: |- A e. ~H
  assume polid.2: |- B e. ~H


  assert |- ( A .ih B ) = ( ( ( ( ( normh ` ( A +h B ) ) ^ 2 ) - ( ( normh ` ( A -h B ) ) ^ 2 ) ) + ( _i x. ( ( ( normh ` ( A +h ( _i .h B ) ) ) ^ 2 ) - ( ( normh ` ( A -h ( _i .h B ) ) ) ^ 2 ) ) ) ) / 4 )

  proof
    cA
    cB
    csp
    co
    cA
    cB
    cva
    co
    #
    @0
    csp
    co
    #
    cA
    cB
    cmv
    co
    #
    @2
    csp
    co
    #
    cmin
    co
    #
    ci
    cA
    ci
    cB
    csm
    co
    #
    cva
    co
    #
    @6
    csp
    co
    #
    cA
    @5
    cmv
    co
    #
    @8
    csp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    @0
    cno
    cfv
    c2
    cexp
    co
    #
    @2
    cno
    cfv
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    @6
    cno
    cfv
    c2
    cexp
    co
    #
    @8
    cno
    cfv
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    cA
    cB
    cB
    cA
    polid.1
    polid.2
    polid.2
    polid.1
    polid2i
    @20
    @12
    c4
    cdiv
    @15
    @4
    @19
    @11
    caddc
    @13
    @1
    @14
    @3
    cmin
    @0
    cA
    cB
    polid.1
    polid.2
    hvaddcli
    normsqi
    @2
    cA
    cB
    polid.1
    polid.2
    hvsubcli
    normsqi
    oveq12i
    @18
    @10
    ci
    cmul
    @16
    @7
    @17
    @9
    cmin
    @6
    cA
    @5
    polid.1
    ci
    cB
    ax-icn
    polid.2
    hvmulcli
    #
    hvaddcli
    normsqi
    @8
    cA
    @5
    polid.1
    @21
    hvsubcli
    normsqi
    oveq12i
    oveq2i
    oveq12i
    oveq1i
    eqtr4i
end
