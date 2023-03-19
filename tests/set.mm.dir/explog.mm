include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cexp.mm"
include "wceq.mm"
include "logcl.mm"
include "efexp.mm"
include "stoic3.mm"
include "eflog.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "eqtr2d.mm"

theorem explog
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ N ) = ( exp ` ( N x. ( log ` A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cN
    cA
    clog
    cfv
    #
    cmul
    co
    ce
    cfv
    #
    @4
    ce
    cfv
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    @0
    @1
    @4
    cc
    wcel
    @2
    @5
    @7
    wceq
    cA
    logcl
    @4
    cN
    efexp
    stoic3
    @3
    @6
    cA
    cN
    cexp
    @0
    @1
    @6
    cA
    wceq
    @2
    cA
    eflog
    3adant3
    oveq1d
    eqtr2d
end
