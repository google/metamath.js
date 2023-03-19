include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cva.mm"
include "caddc.mm"
include "csp.mm"
include "cmul.mm"
include "hvsubcli.mm"
include "normsqi.mm"
include "hvaddcli.mm"
include "oveq12i.mm"
include "oveq2i.mm"
include "hicli.mm"
include "2timesi.mm"
include "eqtri.mm"
include "cneg.mm"
include "cmin.mm"
include "normlem9.mm"
include "addcli.mm"
include "negsubi.mm"
include "eqtr4i.mm"
include "normlem8.mm"
include "negcli.mm"
include "add42i.mm"
include "cc0.mm"
include "negidi.mm"
include "addid1i.mm"
include "add4i.mm"
include "3eqtri.mm"

theorem normpari
  let cA: class A
  let cB: class B
  assume normpar.1: |- A e. ~H
  assume normpar.2: |- B e. ~H


  assert |- ( ( ( normh ` ( A -h B ) ) ^ 2 ) + ( ( normh ` ( A +h B ) ) ^ 2 ) ) = ( ( 2 x. ( ( normh ` A ) ^ 2 ) ) + ( 2 x. ( ( normh ` B ) ^ 2 ) ) )

  proof
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    c2
    cexp
    co
    #
    cA
    cB
    cva
    co
    #
    cno
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    @0
    @0
    csp
    co
    #
    @2
    @2
    csp
    co
    #
    caddc
    co
    #
    c2
    cA
    cno
    cfv
    c2
    cexp
    co
    #
    cmul
    co
    #
    c2
    cB
    cno
    cfv
    c2
    cexp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    @4
    @3
    @5
    caddc
    @0
    cA
    cB
    normpar.1
    normpar.2
    hvsubcli
    normsqi
    @2
    cA
    cB
    normpar.1
    normpar.2
    hvaddcli
    normsqi
    oveq12i
    @11
    cA
    cA
    csp
    co
    #
    @12
    caddc
    co
    #
    cB
    cB
    csp
    co
    #
    @14
    caddc
    co
    #
    caddc
    co
    #
    @6
    @8
    @13
    @10
    @15
    caddc
    @8
    c2
    @12
    cmul
    co
    @13
    @7
    @12
    c2
    cmul
    cA
    normpar.1
    normsqi
    oveq2i
    @12
    cA
    cA
    normpar.1
    normpar.1
    hicli
    #
    2timesi
    eqtri
    @10
    c2
    @14
    cmul
    co
    @15
    @9
    @14
    c2
    cmul
    cB
    normpar.2
    normsqi
    oveq2i
    @14
    cB
    cB
    normpar.2
    normpar.2
    hicli
    #
    2timesi
    eqtri
    oveq12i
    @6
    @12
    @14
    caddc
    co
    #
    cA
    cB
    csp
    co
    #
    cB
    cA
    csp
    co
    #
    caddc
    co
    #
    cneg
    #
    caddc
    co
    #
    @19
    @22
    caddc
    co
    #
    caddc
    co
    @19
    @19
    caddc
    co
    #
    @22
    @23
    caddc
    co
    #
    caddc
    co
    #
    @16
    @4
    @24
    @5
    @25
    caddc
    @4
    @19
    @22
    cmin
    co
    @24
    cA
    cB
    cA
    cB
    normpar.1
    normpar.2
    normpar.1
    normpar.2
    normlem9
    @19
    @22
    @12
    @14
    @17
    @18
    addcli
    #
    @20
    @21
    cA
    cB
    normpar.1
    normpar.2
    hicli
    cB
    cA
    normpar.2
    normpar.1
    hicli
    addcli
    #
    negsubi
    eqtr4i
    cA
    cB
    cA
    cB
    normpar.1
    normpar.2
    normpar.1
    normpar.2
    normlem8
    oveq12i
    @19
    @23
    @19
    @22
    @29
    @22
    @30
    negcli
    @29
    @30
    add42i
    @28
    @26
    cc0
    caddc
    co
    @26
    @16
    @27
    cc0
    @26
    caddc
    @22
    @30
    negidi
    oveq2i
    @26
    @19
    @19
    @29
    @29
    addcli
    addid1i
    @12
    @14
    @12
    @14
    @17
    @18
    @17
    @18
    add4i
    3eqtri
    3eqtri
    eqtr4i
    eqtr4i
end
