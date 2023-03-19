include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "cc0.mm"
include "wi.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "wne.mm"
include "nncn.mm"
include "nnne0.mm"
include "0cxp.mm"
include "syl2anc.mm"
include "0exp.mm"
include "eqtr4d.mm"
include "c1.mm"
include "cif.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "0cn.mm"
include "cxpval.mm"
include "mp2an.mm"
include "eqid.mm"
include "iftruei.mm"
include "3eqtri.mm"
include "0exp0e1.mm"
include "eqtr4i.mm"
include "oveq2.mm"
include "3eqtr4a.mm"
include "jaoi.mm"
include "sylbi.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "adantl.mm"
include "imp.mm"
include "cz.mm"
include "nn0z.mm"
include "cxpexpz.mm"
include "3expa.mm"
include "sylan2.mm"
include "an32s.mm"
include "pm2.61dane.mm"

theorem cxpexp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. NN0 ) -> ( A ^c B ) = ( A ^ B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    cB
    ccxp
    co
    #
    cA
    cB
    cexp
    co
    #
    wceq
    #
    cA
    cc0
    @2
    cA
    cc0
    wceq
    #
    @5
    @1
    @6
    @5
    wi
    @0
    @1
    @5
    @6
    cc0
    cB
    ccxp
    co
    #
    cc0
    cB
    cexp
    co
    #
    wceq
    #
    @1
    cB
    cn
    wcel
    #
    cB
    cc0
    wceq
    #
    wo
    @9
    cB
    elnn0
    @10
    @9
    @11
    @10
    @7
    cc0
    @8
    @10
    cB
    cc
    wcel
    cB
    cc0
    wne
    @7
    cc0
    wceq
    cB
    nncn
    cB
    nnne0
    cB
    0cxp
    syl2anc
    cB
    0exp
    eqtr4d
    @11
    cc0
    cc0
    ccxp
    co
    #
    cc0
    cc0
    cexp
    co
    #
    @7
    @8
    @12
    c1
    @13
    @12
    cc0
    cc0
    wceq
    #
    @14
    c1
    cc0
    cif
    #
    cc0
    cc0
    clog
    cfv
    cmul
    co
    ce
    cfv
    #
    cif
    #
    @15
    c1
    cc0
    cc
    wcel
    #
    @18
    @12
    @17
    wceq
    0cn
    0cn
    cc0
    cc0
    cxpval
    mp2an
    @14
    @15
    @16
    cc0
    eqid
    #
    iftruei
    @14
    c1
    cc0
    @19
    iftruei
    3eqtri
    0exp0e1
    eqtr4i
    cB
    cc0
    cc0
    ccxp
    oveq2
    cB
    cc0
    cc0
    cexp
    oveq2
    3eqtr4a
    jaoi
    sylbi
    @6
    @3
    @7
    @4
    @8
    cA
    cc0
    cB
    ccxp
    oveq1
    cA
    cc0
    cB
    cexp
    oveq1
    eqeq12d
    syl5ibrcom
    adantl
    imp
    @0
    cA
    cc0
    wne
    #
    @1
    @5
    @1
    @0
    @20
    wa
    cB
    cz
    wcel
    #
    @5
    cB
    nn0z
    @0
    @20
    @21
    @5
    cA
    cB
    cxpexpz
    3expa
    sylan2
    an32s
    pm2.61dane
end
