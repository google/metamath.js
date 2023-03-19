include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "crp.mm"
include "w3a.mm"
include "clog.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "ce.mm"
include "cmul.mm"
include "wceq.mm"
include "logcl.mm"
include "3adant3.mm"
include "cr.mm"
include "relogcl.mm"
include "3ad2ant3.mm"
include "recnd.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eflog.mm"
include "reeflog.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "crn.mm"
include "logrncl.mm"
include "logrnaddcl.mm"
include "logef.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem logmul2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. RR+ ) -> ( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) ) )

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
    caddc
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
    cmul
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
    cmul
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
    @3
    @5
    @2
    @0
    @5
    cr
    wcel
    #
    @1
    cB
    relogcl
    3ad2ant3
    #
    recnd
    @4
    @5
    efadd
    syl2anc
    @3
    @10
    cA
    @11
    cB
    cmul
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
    #
    @8
    @6
    wceq
    @3
    @4
    @16
    wcel
    #
    @14
    @17
    @0
    @1
    @18
    @2
    cA
    logrncl
    3adant3
    @15
    @4
    @5
    logrnaddcl
    syl2anc
    @6
    logef
    syl
    eqtr3d
end
