include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "crp.mm"
include "w3a.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "ce.mm"
include "cdiv.mm"
include "wceq.mm"
include "logcl.mm"
include "3adant3.mm"
include "cr.mm"
include "relogcl.mm"
include "3ad2ant3.mm"
include "recnd.mm"
include "efsub.mm"
include "syl2anc.mm"
include "eflog.mm"
include "reeflog.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "crn.mm"
include "cneg.mm"
include "caddc.mm"
include "negsubd.mm"
include "logrncl.mm"
include "renegcld.mm"
include "logrnaddcl.mm"
include "eqeltrrd.mm"
include "logef.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem logdiv2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. RR+ ) -> ( log ` ( A / B ) ) = ( ( log ` A ) - ( log ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    crp
    wcel
    #
    w3a
    #
    cA
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cmin
    co
    #
    ce
    cfv
    #
    clog
    cfv
    #
    cA
    cB
    cdiv
    co
    #
    clog
    cfv
    @6
    @3
    @7
    @9
    clog
    @3
    @7
    @4
    ce
    cfv
    #
    @5
    ce
    cfv
    #
    cdiv
    co
    #
    @9
    @3
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    @7
    @12
    wceq
    @0
    @1
    @13
    @2
    cA
    logcl
    3adant3
    #
    @3
    @5
    @2
    @0
    @5
    cr
    wcel
    @1
    cB
    relogcl
    3ad2ant3
    #
    recnd
    #
    @4
    @5
    efsub
    syl2anc
    @3
    @10
    cA
    @11
    cB
    cdiv
    @0
    @1
    @10
    cA
    wceq
    @2
    cA
    eflog
    3adant3
    @2
    @0
    @11
    cB
    wceq
    @1
    cB
    reeflog
    3ad2ant3
    oveq12d
    eqtrd
    fveq2d
    @3
    @6
    clog
    crn
    #
    wcel
    @8
    @6
    wceq
    @3
    @4
    @5
    cneg
    #
    caddc
    co
    #
    @6
    @17
    @3
    @4
    @5
    @14
    @16
    negsubd
    @3
    @4
    @17
    wcel
    #
    @18
    cr
    wcel
    @19
    @17
    wcel
    @0
    @1
    @20
    @2
    cA
    logrncl
    3adant3
    @3
    @5
    @15
    renegcld
    @4
    @18
    logrnaddcl
    syl2anc
    eqeltrrd
    @6
    logef
    syl
    eqtr3d
end
